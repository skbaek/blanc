#!/usr/bin/env swipl

:- initialization(main, main).
:- ['$PRELUDE'].

read_file_to_lines(NAME, LINES) :-
  read_file_to_string(NAME, STR, []),
  split_string(STR, "\n", "", LINES).

uppercase('A').
uppercase('B').
uppercase('C').
uppercase('D').
uppercase('E').
uppercase('F').
uppercase('G').
uppercase('H').
uppercase('I').
uppercase('J').
uppercase('K').
uppercase('L').
uppercase('M').
uppercase('N').
uppercase('O').
uppercase('P').
uppercase('Q').
uppercase('R').
uppercase('S').
uppercase('T').
uppercase('U').
uppercase('V').
uppercase('W').
uppercase('X').
uppercase('Y').
uppercase('Z').

lowercase('a').
lowercase('b').
lowercase('c').
lowercase('d').
lowercase('e').
lowercase('f').
lowercase('g').
lowercase('h').
lowercase('i').
lowercase('j').
lowercase('k').
lowercase('l').
lowercase('m').
lowercase('n').
lowercase('o').
lowercase('p').
lowercase('q').
lowercase('r').
lowercase('s').
lowercase('t').
lowercase('u').
lowercase('v').
lowercase('w').
lowercase('x').
lowercase('y').
lowercase('z').

letter(CHAR) :- uppercase(CHAR).
letter(CHAR) :- lowercase(CHAR).

digit('0').
digit('1').
digit('2').
digit('3').
digit('4').
digit('5').
digit('6').
digit('7').
digit('8').
digit('9').

valid_char(CHAR) :- letter(CHAR).
valid_char(CHAR) :- digit(CHAR).
valid_char('\'').
valid_char('.').
valid_char('ℕ').
valid_char('₀').
valid_char('₁').
valid_char('₂').
valid_char('₃').
valid_char('₄').
valid_char('₅').
valid_char('₆').
valid_char('₇').
valid_char('₈').
valid_char('₉').
valid_char('!').
valid_char('?').
valid_char('φ').
valid_char('ξ').
valid_char('σ').
valid_char('ρ').
valid_char('υ').
valid_char('_').
valid_char('Θ').
valid_char('Λ').
valid_char('α').
valid_char('Ξ').
valid_char('ₙ').

valid_string(ATOM) :- string_chars(ATOM, CHARS), maplist(valid_char, CHARS).
  
check_tokens(TOKENS) :- maplist(valid_string, TOKENS).
check_tokens(TOKENS) :- 
  format("Invalid tokens : ~w", [TOKENS]),
  throw(validity_fail).

break(LINE, WORDS) :- 
  split_string(LINE, " ,;^\"~⊚¬·{}⟨⟩±∅()[]⟪⟫*+-⊻↟≥\\⊢:×&=←$#π∘λ⦃⦄∃/∨∈∀@<≤`|>∧≠→⟦↦↔⟧%", "", TEMP),
  delete(TEMP, "", WORDS).

is_comment(STR) :- string_concat("--", _, STR), !.
is_comment(STR) :- string_concat(" ", SFX, STR), is_comment(SFX), !.

inert(STR) :- is_comment(STR), !.
% inert(STR) :- string_concat("#", _, STR).
% inert(STR) :- string_concat("%", _, STR).
inert(STR) :- string_concat("namespace", _, STR), !.
inert(STR) :- string_concat("open", _, STR), !.
inert(STR) :- string_concat("import", _, STR), !.
inert("end").
inert("").

primitive("_").
primitive("rcases").
primitive("apply").
primitive("by").
primitive("with").
primitive("if").
primitive("then").
primitive("else").
primitive("refine").
primitive("intros").
primitive("cases").
primitive("simp").
primitive("intros").
primitive("exact").
primitive("intro").
primitive("only").
primitive("rw").
primitive("unfold").
primitive("constructor").
primitive("first").
primitive("rw").
primitive("tactic").
primitive("have").
primitive("match").
primitive("macro_rules").

line_decl(["macro", NAME | _], NAME).
line_decl(["def", NAME | _], NAME).
line_decl(["definition", NAME | _], NAME).
line_decl(["partial", "def", NAME | _], NAME).
line_decl(["partial", "definition", NAME | _], NAME).
line_decl(["lemma", NAME | _], NAME).
line_decl(["theorem", NAME | _], NAME).
line_decl(["inductive", NAME | _], NAME).
line_decl(["structure", NAME | _], NAME).
line_decl(["abbrev", NAME | _], NAME).
line_decl(["syntax", NAME | _], NAME).
line_decl(["elab", NAME | _], NAME).
line_decl(["class", NAME | _], NAME).

line_name_rest(["macro", NAME | REST], NAME, REST).
line_name_rest(["def", NAME | REST], NAME, REST).
line_name_rest(["definition", NAME | REST], NAME, REST).
line_name_rest(["partial", "def", NAME | REST], NAME, REST).
line_name_rest(["partial", "definition", NAME | REST], NAME, REST).
line_name_rest(["lemma", NAME | REST], NAME, REST).
line_name_rest(["theorem", NAME | REST], NAME, REST).
line_name_rest(["inductive", NAME | REST], NAME, REST).
line_name_rest(["structure", NAME | REST], NAME, REST).
line_name_rest(["abbrev", NAME | REST], NAME, REST).
line_name_rest(["syntax", NAME | REST], NAME, REST).
line_name_rest(["elab", NAME | REST], NAME, REST).
line_name_rest(["class", NAME | REST], NAME, REST).

add_all([], TREE, TREE).
add_all([TOKEN | TOKENS], TREE, NEW_TREE) :- 
  rb_insert(TREE, TOKEN, c, TEMP), !,
  add_all(TOKENS, TEMP, NEW_TREE).

decl_used(DECL, TREE) :- rb_in(DECL, c, TREE), !.
decl_used(DECL, TREE) :-  
  split_string(DECL, ".", "", [_, TAIL]), !, 
  rb_in(TAIL, c, TREE).

loop(_, []).
loop(TREE, [LINE | LINES]) :- 
  line_decl(LINE, DECL), !, 
  (
    decl_used(DECL, TREE) -> 
    loop(TREE, LINES)
  ;
    format("Unused : ~w", [DECL]),
    throw(unused_def)
  ).
loop(TREE, [LINE | LINES]) :-
  add_all(LINE, TREE, NEW_TREE), !,
    loop(NEW_TREE, LINES).

rep(_, []).
rep(TREE, [decl(NAME, TOKENS) | DECLS]) :- 
    decl_used(NAME, TREE) -> 
    add_all(TOKENS, TREE, NEW_TREE), !,
    rep(NEW_TREE, DECLS)
  ;
    format("Unused : ~w", [NAME]),
    throw(unused_def).

header(LINE) :- line_decl(LINE, _).
header(["instance" | _]).
header(["notation" | _]).
header(["infix" | _]).
header(["infixr" | _]).

carve([], [], []).
carve([LINE | LINES], [], [[LINE | BODY] | DECLS]) :- 
  header(LINE), !, 
  carve(LINES, BODY, DECLS).
carve([LINE | LINES], [LINE | BODY], DECLS) :- 
  carve(LINES, BODY, DECLS).

gather([LINE | LINES], decl(NAME, TOKENS)) :- 
  line_name_rest(LINE, NAME, REST), !, 
  append([REST | LINES], TOKENS).

gather([[_ | REST] | LINES], decl("null", TOKENS)) :- 
  append([REST | LINES], TOKENS).

gather(LINES, _) :- 
  write_ln("FAILED!:"), 
  write_list(LINES),
  throw(gather_fail).

main :- 
  % read_file_to_lines('Basic.lean', BASIC),
  % read_file_to_lines('Semantics.lean', SEM),
  % read_file_to_lines('Common.lean', COMMON),
  % read_file_to_lines('Weth.lean', WETH),
  % read_file_to_lines('Solvent.lean', SOLV),
  % append([BASIC, SEM, COMMON, WETH, SOLV], L0),
  read_file_to_lines('Temp.lean', L0),
  exclude(inert, L0, L1),
  maplist(break, L1, L2),
  maplist(exclude(primitive), L2, LINES),
  carve(LINES, [], LINESS),
  maplist(gather, LINESS, REV),
  reverse(REV, DECLS),
  rb_new(EMPTY),
  add_all(
    [
      "main",
      "withoutPosition",
      "transaction_inv_solvent",
      "ArgType.toString",
      "Bits.bexp",
      "Bits.toHex",
      "Bytes.toHex",
      "Bits.toB256",
      "Bits.toB64",
      "Bits.toB128",
      "Nat.toWord'",
      "Ninst.add", 
      "Ninst.mul", 
      "Ninst.sub", 
      "Ninst.div", 
      "Ninst.sdiv", 
      "Ninst.mod", 
      "Ninst.smod", 
      "Ninst.addmod", 
      "Ninst.mulmod", 
      "Ninst.exp", 
      "Ninst.signextend", 
      "Ninst.lt", 
      "Ninst.gt", 
      "Ninst.slt", 
      "Ninst.sgt", 
      "Ninst.eq", 
      "Ninst.iszero", 
      "Ninst.and", 
      "Ninst.or", 
      "Ninst.xor", 
      "Ninst.not", 
      "Ninst.byte", 
      "Ninst.shr", 
      "Ninst.shl", 
      "Ninst.sar", 
      "Ninst.kec", 
      "Ninst.address", 
      "Ninst.balance", 
      "Ninst.origin", 
      "Ninst.caller", 
      "Ninst.callvalue", 
      "Ninst.calldataload", 
      "Ninst.calldatasize", 
      "Ninst.calldatacopy", 
      "Ninst.codesize", 
      "Ninst.codecopy", 
      "Ninst.gasprice", 
      "Ninst.extcodesize", 
      "Ninst.extcodecopy", 
      "Ninst.retdatasize", 
      "Ninst.retdatacopy", 
      "Ninst.extcodehash", 
      "Ninst.blockhash", 
      "Ninst.coinbase", 
      "Ninst.timestamp", 
      "Ninst.number", 
      "Ninst.prevrandao", 
      "Ninst.gaslimit", 
      "Ninst.chainid", 
      "Ninst.selfbalance", 
      "Ninst.basefee", 
      "Ninst.blobhash", 
      "Ninst.blobbasefee", 
      "Ninst.pop", 
      "Ninst.mload", 
      "Ninst.mstore", 
      "Ninst.mstore8", 
      "Ninst.sload", 
      "Ninst.sstore", 
      "Ninst.tload", 
      "Ninst.tstore", 
      "Ninst.mcopy", 
      "Ninst.pc", 
      "Ninst.msize", 
      "Ninst.gas", 
      "Ninst.dup", 
      "Ninst.swap", 
      "Ninst.log", 
      "Ninst.create", 
      "Ninst.call", 
      "Ninst.callcode", 
      "Ninst.delcall", 
      "Ninst.create2", 
      "Ninst.statcall", 
      "Bytes.keccak", 
      "Bytes.toB8L", 
      "RLP.toStrings", 
      "RLPs.encode", 
      "RLP.encode", 
      "RLP.encodeBytes", 
      "RLP.decode", 
      "RLPs.decode", 
      "String.keccak", 
      "null"
    ], 
    EMPTY, 
    TREE
  ),
  rep(TREE, DECLS).

