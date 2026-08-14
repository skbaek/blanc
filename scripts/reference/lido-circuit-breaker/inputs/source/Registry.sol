// SPDX-FileCopyrightText: 2026 Lido <info@lido.fi>
// SPDX-License-Identifier: GPL-3.0
pragma solidity 0.8.34;

/// @title  Registry
/// @author Lido
/// @notice Library for managing an enumerable pausable-pauser registry.
library Registry {
    // =========================================================================
    // Types
    // =========================================================================

    /// @dev Pausable-to-pauser registry with an enumerable set of pausables.
    ///      Each pausable has one pauser, but a pauser can be registered for many pausables.
    ///      A separate counter (pausableCount) is kept per pauser so that isRegistered() can
    ///      answer in O(1) instead of looping over the pausables array.
    struct Storage {
        mapping(address pausable => address pauser) pauser;
        mapping(address pausable => uint256 oneBasedIndex) oneBasedIndex;
        address[] pausables;
        mapping(address pauser => uint256 pausableCount) pausableCount;
    }

    // =========================================================================
    // Events
    // =========================================================================

    event PauserSet(address indexed pausable, address indexed previousPauser, address indexed newPauser);

    // =========================================================================
    // Errors
    // =========================================================================

    error PausableZero();

    // =========================================================================
    // View functions
    // =========================================================================

    /// @dev    Return the address of the pauser registered for a pausable.
    /// @param  _pausable Pausable contract address.
    /// @return Pauser address, or zero if not registered.
    function getPauser(Storage storage _self, address _pausable) internal view returns (address) {
        return _self.pauser[_pausable];
    }

    /// @dev    Return an array of all currently registered pausables.
    /// @return Array of pausable addresses.
    function getPausables(Storage storage _self) internal view returns (address[] memory) {
        return _self.pausables;
    }

    /// @dev    Return the number of pausables registered to a pauser.
    /// @param  _pauser Pauser address.
    /// @return Number of pausables.
    function getPausableCount(Storage storage _self, address _pauser) internal view returns (uint256) {
        return _self.pausableCount[_pauser];
    }

    /// @dev    Return whether an address is currently registered for at least one pausable.
    /// @param  _pauser Address to check.
    /// @return True if the address has at least one pausable registered.
    function isRegistered(Storage storage _self, address _pauser) internal view returns (bool) {
        return _self.pausableCount[_pauser] > 0;
    }

    // =========================================================================
    // Write functions
    // =========================================================================

    /// @dev    Register, replace, or unregister a pauser for a pausable.
    ///         - Register:   previousPauser == 0, _newPauser != 0
    ///         - Replace:    previousPauser != 0, _newPauser != 0
    ///         - Unregister: previousPauser != 0, _newPauser == 0
    ///
    ///         Unregistration is idempotent: setting zero on an already-zero pauser succeeds
    ///         (with an event) instead of reverting. Without this, a pauser could grief the admin
    ///         by frontrunning the unregistration tx with a pause() call, which clears the mapping
    ///         and would make the admin's transaction revert.
    /// @param  _pausable  Pausable contract address.
    /// @param  _newPauser New pauser address. Use address(0) to unregister.
    function setPauser(Storage storage _self, address _pausable, address _newPauser) internal {
        require(_pausable != address(0), PausableZero());

        address previousPauser = _self.pauser[_pausable];

        // Update the pauser.
        _self.pauser[_pausable] = _newPauser;

        // If replacing or unregistering, decrement the old pauser's pausable count.
        // Otherwise this is a new pausable, so add it to the set.
        if (previousPauser != address(0)) {
            --_self.pausableCount[previousPauser];
        } else {
            _self.pausables.push(_pausable);
            _self.oneBasedIndex[_pausable] = _self.pausables.length;
        }

        // If registering or replacing, increment the new pauser's pausable count.
        // Otherwise this is an unregistration, so remove the pausable from the set.
        if (_newPauser != address(0)) {
            ++_self.pausableCount[_newPauser];
        } else {
            uint256 removedIndex = _self.oneBasedIndex[_pausable];
            address lastPausable = _self.pausables[_self.pausables.length - 1];

            _self.pausables[removedIndex - 1] = lastPausable;
            _self.oneBasedIndex[lastPausable] = removedIndex;

            _self.pausables.pop();
            delete _self.oneBasedIndex[_pausable];
        }

        emit PauserSet(_pausable, previousPauser, _newPauser);
    }
}
