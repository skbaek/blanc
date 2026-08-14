// SPDX-FileCopyrightText: 2026 Lido <info@lido.fi>
// SPDX-License-Identifier: GPL-3.0
pragma solidity 0.8.34;

import {Registry} from "./Registry.sol";

/// @title  IPausable
/// @notice Interface pausable contracts must implement for CircuitBreaker compatibility.
interface IPausable {
    /// @notice Whether the contract is currently paused.
    function isPaused() external view returns (bool);

    /// @notice Pause the contract for a given duration.
    /// @param  _duration Duration in seconds.
    function pauseFor(uint256 _duration) external;
}

/// @title  CircuitBreaker
/// @author Lido
/// @notice Emergency pause manager for pausable contracts.
/// @dev    Some setups (e.g. a DAO with on-chain voting) cannot respond fast enough
///         in emergency situations. This contract lets the admin delegate pause authority to
///         designated pausers that can act instantly.
///
///         Design:
///         - Immutable admin to avoid ownership exploits/mistakes.
///         - One pauser per pausable for clear accountability.
///         - Single-use pause minimizes damage if pauser is compromised.
///         - Same pause duration for all contracts because the admin's reaction time depends
///           on the governance timelines, not on the individual contract.
///         - Pausers must periodically heartbeat to prove liveness. Each heartbeat extends
///           their authorization window. A committee that cannot prove its liveness should not
///           be trusted to respond in an emergency.
///
///         Trust assumptions:
///         - Admin is always honest.
///         - Pausable is a trusted contract upon registration.
///         - Pauser is a trusted multisig committee upon registration.
contract CircuitBreaker {
    using Registry for Registry.Storage;

    // =========================================================================
    // Immutables
    // =========================================================================

    /// @notice Admin address.
    address public immutable ADMIN;

    /// @notice Inclusive lower bound for pauseDuration in seconds.
    uint256 public immutable MIN_PAUSE_DURATION;

    /// @notice Inclusive upper bound for pauseDuration in seconds.
    uint256 public immutable MAX_PAUSE_DURATION;

    /// @notice Inclusive lower bound for heartbeatInterval in seconds.
    uint256 public immutable MIN_HEARTBEAT_INTERVAL;

    /// @notice Inclusive upper bound for heartbeatInterval in seconds.
    uint256 public immutable MAX_HEARTBEAT_INTERVAL;

    // =========================================================================
    // State variables
    // =========================================================================

    /// @notice Duration in seconds of the pause applied to the pausable on trigger.
    uint256 public pauseDuration;

    /// @notice Time window in seconds since last heartbeat within which a pauser is considered authorized.
    uint256 public heartbeatInterval;

    /// @notice Timestamp after which a pauser is no longer authorized to heartbeat or pause.
    mapping(address pauser => uint256 timestamp) public heartbeatExpiry;

    /// @dev    Tracks pausable-to-pauser registrations.
    Registry.Storage internal registry;

    /// @dev    Reentrancy guard that prevents a malicious pausable from reentering
    ///         to trigger a pause on a different pausable.
    bool internal transient lock;

    // =========================================================================
    // Events
    // =========================================================================

    event CircuitBreakerInitialized(
        address indexed admin,
        uint256 minPauseDuration,
        uint256 maxPauseDuration,
        uint256 minHeartbeatInterval,
        uint256 maxHeartbeatInterval
    );

    event PauseDurationUpdated(uint256 previousPauseDuration, uint256 newPauseDuration);
    event HeartbeatIntervalUpdated(uint256 previousHeartbeatInterval, uint256 newHeartbeatInterval);
    event HeartbeatUpdated(address indexed pauser, uint256 newHeartbeatExpiry);
    event PauseTriggered(address indexed pausable, address indexed pauser, uint256 pauseDuration);

    // =========================================================================
    // Errors
    // =========================================================================

    error SenderNotAdmin();
    error SenderNotPauser();

    error AdminZero();

    error MinPauseDurationZero();
    error MinPauseDurationExceedsMax();

    error PauseDurationBelowMin();
    error PauseDurationAboveMax();

    error MinHeartbeatIntervalZero();
    error MinHeartbeatIntervalExceedsMax();

    error HeartbeatIntervalBelowMin();
    error HeartbeatIntervalAboveMax();

    error HeartbeatExpired();
    error PauseFailed();
    error ReentrantCall();

    // =========================================================================
    // Modifiers
    // =========================================================================

    modifier nonReentrant() {
        require(!lock, ReentrantCall());
        lock = true;
        _;
        lock = false;
    }

    modifier onlyAdmin() {
        require(msg.sender == ADMIN, SenderNotAdmin());
        _;
    }

    // =========================================================================
    // Constructor
    // =========================================================================

    /// @param _admin                    Admin address.
    /// @param _minPauseDuration         Inclusive lower bound for pause duration.
    /// @param _maxPauseDuration         Inclusive upper bound for pause duration.
    /// @param _minHeartbeatInterval     Inclusive lower bound for heartbeat interval.
    /// @param _maxHeartbeatInterval     Inclusive upper bound for heartbeat interval.
    /// @param _initialPauseDuration     Initial pause duration.
    /// @param _initialHeartbeatInterval Initial heartbeat interval.
    constructor(
        address _admin,
        uint256 _minPauseDuration,
        uint256 _maxPauseDuration,
        uint256 _minHeartbeatInterval,
        uint256 _maxHeartbeatInterval,
        uint256 _initialPauseDuration,
        uint256 _initialHeartbeatInterval
    ) {
        require(_admin != address(0), AdminZero());
        require(_minPauseDuration != 0, MinPauseDurationZero());
        require(_minPauseDuration <= _maxPauseDuration, MinPauseDurationExceedsMax());
        require(_minHeartbeatInterval != 0, MinHeartbeatIntervalZero());
        require(_minHeartbeatInterval <= _maxHeartbeatInterval, MinHeartbeatIntervalExceedsMax());

        ADMIN = _admin;
        MIN_PAUSE_DURATION = _minPauseDuration;
        MAX_PAUSE_DURATION = _maxPauseDuration;
        MIN_HEARTBEAT_INTERVAL = _minHeartbeatInterval;
        MAX_HEARTBEAT_INTERVAL = _maxHeartbeatInterval;

        emit CircuitBreakerInitialized(
            _admin, _minPauseDuration, _maxPauseDuration, _minHeartbeatInterval, _maxHeartbeatInterval
        );

        _setPauseDuration(_initialPauseDuration);
        _setHeartbeatInterval(_initialHeartbeatInterval);
    }

    // =========================================================================
    // View functions
    // =========================================================================

    /// @notice Return the pauser registered for a pausable.
    /// @param  _pausable Pausable contract address.
    /// @return Pauser address, or zero if not registered.
    function getPauser(address _pausable) external view returns (address) {
        return registry.getPauser(_pausable);
    }

    /// @notice Return all pausable addresses currently registered.
    /// @return Array of pausable addresses.
    function getPausables() external view returns (address[] memory) {
        return registry.getPausables();
    }

    /// @notice Return the number of pausables assigned to a pauser.
    /// @param  _pauser Pauser address.
    /// @return Number of pausables.
    function getPausableCount(address _pauser) external view returns (uint256) {
        return registry.getPausableCount(_pauser);
    }

    /// @notice Return whether a pauser is live and registered to at least one pausable.
    /// @param  _pauser Pauser address.
    /// @return True if the heartbeat has not expired.
    function isPauserLive(address _pauser) public view returns (bool) {
        return block.timestamp < heartbeatExpiry[_pauser];
    }

    // =========================================================================
    // Admin functions
    // =========================================================================

    /// @notice Set the pause duration applied on pause.
    /// @param  _newPauseDuration New duration in seconds.
    function setPauseDuration(uint256 _newPauseDuration) external onlyAdmin {
        _setPauseDuration(_newPauseDuration);
    }

    /// @notice Set the heartbeat interval pausers must maintain to remain active.
    /// @param  _newHeartbeatInterval New interval in seconds.
    function setHeartbeatInterval(uint256 _newHeartbeatInterval) external onlyAdmin {
        _setHeartbeatInterval(_newHeartbeatInterval);
    }

    /// @notice Register, replace, or unregister a pauser for a pausable.
    ///         - The previous pauser is overwritten. If they have no remaining pausables,
    ///           their heartbeat expiry is cleared.
    ///         - The new pauser's heartbeat expiry is extended on registration.
    /// @dev    Does not verify CircuitBreaker has pause permission on the pausable or that the
    ///         pausable implements the correct interface. These properties can change after
    ///         registration (e.g. the pausable revokes the role, implementation changes via proxy upgrade).
    /// @param  _pausable Pausable contract address.
    /// @param  _newPauser New pauser address. Zero unregisters the pauser.
    function registerPauser(address _pausable, address _newPauser) external onlyAdmin {
        address previousPauser = registry.getPauser(_pausable);
        registry.setPauser(_pausable, _newPauser);

        if (previousPauser != address(0) && !registry.isRegistered(previousPauser)) {
            _setHeartbeatExpiry(previousPauser, 0);
        }

        if (_newPauser != address(0)) {
            _setHeartbeatExpiry(_newPauser, block.timestamp + heartbeatInterval);
        }
    }

    // =========================================================================
    // Pauser functions
    // =========================================================================

    /// @notice Record a liveness proof to remain authorized to pause.
    function heartbeat() external {
        require(registry.isRegistered(msg.sender), SenderNotPauser());
        require(isPauserLive(msg.sender), HeartbeatExpired());

        _setHeartbeatExpiry(msg.sender, block.timestamp + heartbeatInterval);
    }

    /// @notice Pause a pausable contract. The pausable must implement IPausable and must have
    ///         granted CircuitBreaker the pause role.
    ///         Single-use: the caller is unregistered from this pausable after a successful
    ///         pause. Their heartbeat expiry is extended if they still have other
    ///         pausables registered, or cleared otherwise.
    /// @param  _pausable Pausable contract to pause.
    function pause(address _pausable) external nonReentrant {
        require(msg.sender == registry.getPauser(_pausable), SenderNotPauser());
        require(isPauserLive(msg.sender), HeartbeatExpired());

        uint256 duration = pauseDuration;
        IPausable target = IPausable(_pausable);

        registry.setPauser(_pausable, address(0));
        target.pauseFor(duration);
        require(target.isPaused(), PauseFailed());
        emit PauseTriggered(_pausable, msg.sender, duration);

        _setHeartbeatExpiry(msg.sender, registry.isRegistered(msg.sender) ? block.timestamp + heartbeatInterval : 0);
    }

    // =========================================================================
    // Internal functions
    // =========================================================================

    /// @dev    Sets the heartbeat expiry.
    /// @param  _pauser Pauser address.
    /// @param  _expiry New heartbeat expiry timestamp.
    function _setHeartbeatExpiry(address _pauser, uint256 _expiry) internal {
        heartbeatExpiry[_pauser] = _expiry;

        emit HeartbeatUpdated(_pauser, _expiry);
    }

    /// @dev    Sets the pause duration. Reverts if outside [MIN, MAX] bounds.
    /// @param  _newPauseDuration New duration in seconds.
    function _setPauseDuration(uint256 _newPauseDuration) internal {
        require(_newPauseDuration >= MIN_PAUSE_DURATION, PauseDurationBelowMin());
        require(_newPauseDuration <= MAX_PAUSE_DURATION, PauseDurationAboveMax());

        emit PauseDurationUpdated(pauseDuration, _newPauseDuration);

        pauseDuration = _newPauseDuration;
    }

    /// @dev    Sets the heartbeat interval. Reverts if outside [MIN, MAX] bounds.
    /// @param  _newHeartbeatInterval New interval in seconds.
    function _setHeartbeatInterval(uint256 _newHeartbeatInterval) internal {
        require(_newHeartbeatInterval >= MIN_HEARTBEAT_INTERVAL, HeartbeatIntervalBelowMin());
        require(_newHeartbeatInterval <= MAX_HEARTBEAT_INTERVAL, HeartbeatIntervalAboveMax());

        emit HeartbeatIntervalUpdated(heartbeatInterval, _newHeartbeatInterval);

        heartbeatInterval = _newHeartbeatInterval;
    }
}
