'use strict';

const test = require('node:test');
const assert = require('node:assert/strict');
const { analyzeGrammar } = require('../src/lr1');
const { parseGrammarSpec } = require('../src/grammar');

function build(spec) {
  const parsed = parseGrammarSpec(spec);
  assert.equal(parsed.ok, true, parsed.errors.map((e) => e.message).join('; '));
  return analyzeGrammar(parsed.grammar);
}

const CABLE_GRAMMAR = {
  terminals: 'a b c d e',
  nonterminals: 'S A B',
  start: 'S',
  // Four S rules: starting with a/b, through A/B, ending in d/e; A and B both derive c.
  productions: 'S -> a A d\nS -> a B e\nS -> b A e\nS -> b B d\nA -> c\nB -> c',
};

test('cable-control grammar is conflict free with exactly 14 canonical LR(1) states', () => {
  const a = build(CABLE_GRAMMAR);
  assert.equal(a.conflictFree, true);
  assert.equal(a.conflictCount, 0);
  assert.equal(a.states.length, 14);
  // "empty conflict" evidence: firstConflict must be absent, not merely hidden.
  assert.equal(a.firstConflict, null);

  // ACTION table: no cell may carry competing actions (notably no r/r pair).
  for (const row of a.actionTable) {
    for (const [t, acts] of Object.entries(row.actions)) {
      assert.equal(acts.length, 1, `state I${row.state} on ${t} has competing actions`);
      const reduces = acts.filter((x) => x.type === 'reduce').length;
      assert.ok(reduces <= 1, `state I${row.state} on ${t} has competing reductions`);
    }
  }

  // The two states reached after `a c` (I6) and `b c` (I9) share the same core
  // but carry different lookaheads; canonical LR(1) keeps them distinct, which
  // is exactly what removes the LALR-style false reduce/reduce conflict.
  const itemTexts = (s) => s.items.map((i) => i.text).sort();
  assert.deepEqual(itemTexts(a.states[6]), ['A -> c · , d', 'B -> c · , e']);
  assert.deepEqual(itemTexts(a.states[9]), ['A -> c · , e', 'B -> c · , d']);
});

test('cable-control items, transitions and ACTION/GOTO mutually reconcile', () => {
  const a = build(CABLE_GRAMMAR);
  const rhsOf = (it) => {
    const p = a.productions.find((x) => (x.augmented ? 0 : x.index) === it.prod);
    return p.rhs;
  };

  for (const st of a.states) {
    // Symbols after a dot equal the outgoing transition symbols.
    const afterDot = new Set();
    for (const it of st.items) {
      const rhs = rhsOf(it);
      if (it.dot < rhs.length) afterDot.add(rhs[it.dot]);
    }
    assert.deepEqual(new Set(Object.keys(st.transitions)), afterDot,
      `I${st.id}: transitions do not match dotted symbols`);

    const row = a.actionTable[st.id];
    // Every terminal transition is a matching shift entry.
    for (const [sym, target] of Object.entries(st.transitions)) {
      if (a.terminals.includes(sym)) {
        assert.equal(row.actions[sym].length, 1);
        assert.deepEqual(row.actions[sym][0], {
          type: 'shift', state: target, text: `shift ${target}`, short: `s${target}`,
        });
      }
    }
    // Every nonterminal transition is a GOTO entry and vice versa.
    for (const n of a.nonterminals) {
      if (st.transitions[n] !== undefined) assert.equal(row.gotos[n], st.transitions[n]);
      else assert.equal(row.gotos[n], undefined);
    }
    // Every completed non-augmented item yields its reduce on its lookahead.
    for (const it of st.items) {
      if (it.dot === rhsOf(it).length && it.prod !== 0) {
        assert.equal(row.actions[it.la][0].type, 'reduce');
        assert.equal(row.actions[it.la][0].production, it.prod);
      }
    }
  }

  // A driver parser fed solely by the emitted ACTION/GOTO tables accepts all
  // four valid sentences — items, transitions and tables therefore reconcile
  // end-to-end rather than merely looking consistent in isolation.
  const parse = (tokens) => {
    const stack = [0];
    const input = tokens.concat('$');
    let steps = 0;
    while (steps++ < 100) {
      const row = a.actionTable[stack[stack.length - 1]];
      const acts = row.actions[input[0]];
      assert.ok(acts && acts.length === 1,
        `parser table cell empty or conflicting in I${row.state} on ${input[0]}`);
      const act = acts[0];
      if (act.type === 'accept') return;
      if (act.type === 'shift') {
        stack.push(act.state);
        input.shift();
      } else {
        const p = a.productions.find((x) => (x.augmented ? 0 : x.index) === act.production);
        stack.length -= p.rhs.length;
        const target = a.actionTable[stack[stack.length - 1]].gotos[p.lhs];
        assert.ok(Number.isInteger(target), `missing GOTO after reducing ${p.text}`);
        stack.push(target);
      }
    }
    throw new Error('parser did not terminate');
  };
  parse(['a', 'c', 'd']);
  parse(['a', 'c', 'e']);
  parse(['b', 'c', 'e']);
  parse(['b', 'c', 'd']);

  // State numbering is stable across repeated constructions.
  const sig = (x) => x.states.map((s) => s.items.map((i) => i.text).sort().join('&')).join('||');
  assert.equal(sig(build(CABLE_GRAMMAR)), sig(a));
});

test('expression grammar is conflict free and has canonical 22 LR(1) states', () => {
  const a = build({
    terminals: 'id + * ( )',
    nonterminals: 'E T F',
    start: 'E',
    productions: 'E -> E + T\nE -> T\nT -> T * F\nT -> F\nF -> ( E )\nF -> id',
  });
  assert.equal(a.conflictFree, true);
  assert.equal(a.conflictCount, 0);
  assert.equal(a.states.length, 22);
  assert.equal(a.firstConflict, null);
});

test('nullable computation handles epsilon chains', () => {
  const a = build({
    terminals: 'a',
    nonterminals: 'S A B C',
    start: 'S',
    productions: 'S -> A a\nA -> B C\nB -> ε\nC ->',
  });
  assert.deepEqual(a.nullable.sort(), ['A', 'B', 'C']);
  assert.ok(!a.nullable.includes('S'));
});

test('FIRST sets include epsilon propagation and terminals', () => {
  const a = build({
    terminals: 'a b',
    nonterminals: 'S A B C',
    start: 'S',
    productions: 'S -> A B a\nA -> ε\nA -> a\nB -> ε\nB -> b\nC -> C a | b',
  });
  assert.deepEqual(a.first.A.sort(), ['a']);
  assert.deepEqual(a.first.B.sort(), ['b']);
  // FIRST(S) contains a (from a) and b (via B)
  assert.deepEqual(a.first.S.sort(), ['a', 'b']);
  assert.deepEqual(a.first.C.sort(), ['b']);
});

test('left-recursive grammar with epsilon: nullable FIRST used in closure', () => {
  // A -> A α | ε style with terminal
  const a = build({
    terminals: 'x',
    nonterminals: 'L',
    start: 'L',
    productions: 'L -> L x\nL -> ε',
  });
  assert.equal(a.conflictFree, true);
  assert.deepEqual(a.nullable, ['L']);
  assert.deepEqual(a.first.L, ['x']);
});

test('exactly one accept action on $ in the whole table', () => {
  const a = build({
    terminals: 'id +',
    nonterminals: 'E',
    start: 'E',
    productions: 'E -> E + id\nE -> id',
  });
  let accepts = 0;
  for (const row of a.actionTable) {
    for (const acts of Object.values(row.actions)) {
      if (acts.some((x) => x.type === 'accept')) accepts += 1;
    }
  }
  assert.equal(accepts, 1);
});

test('shift/reduce conflict reports state, lookahead, competing items and prefix', () => {
  const a = build({
    terminals: 'id +',
    nonterminals: 'E',
    start: 'E',
    productions: 'E -> E + E\nE -> id',
  });
  assert.equal(a.conflictFree, false);
  const c = a.firstConflict;
  assert.equal(c.type, 'shift-reduce');
  assert.equal(c.lookahead, '+');
  const types = c.actions.map((x) => x.type).sort();
  assert.deepEqual(types, ['reduce', 'shift']);
  // Both competing items mention E and the + lookahead.
  const allItems = c.actions.flatMap((x) => x.items);
  assert.ok(allItems.some((i) => i.text.includes('E -> E · + E')));
  assert.ok(allItems.some((i) => i.text.includes('E -> E + E ·')));
  // Prefix evidence is a valid transition path from state 0.
  let s = 0;
  for (const sym of c.prefix.symbols) s = a.states[s].transitions[sym];
  assert.equal(s, c.state);
  assert.deepEqual(c.prefix.states[0], 0);
  assert.deepEqual(c.prefix.states[c.prefix.states.length - 1], c.state);
});

test('dangling-else grammar has a shift/reduce conflict on ELSE', () => {
  const a = build({
    terminals: 'IF THEN ELSE e',
    nonterminals: 'S',
    start: 'S',
    productions: 'S -> IF e THEN S\nS -> IF e THEN S ELSE S\nS -> e',
  });
  assert.equal(a.conflictFree, false);
  assert.equal(a.firstConflict.type, 'shift-reduce');
  assert.equal(a.firstConflict.lookahead, 'ELSE');
  // shortest-prefix evidence reaches the conflict state
  let s = 0;
  for (const sym of a.firstConflict.prefix.symbols) s = a.states[s].transitions[sym];
  assert.equal(s, a.firstConflict.state);
});

test('reduce/reduce conflict orders actions by production number', () => {
  const a = build({
    terminals: 'x',
    nonterminals: 'S A B',
    start: 'S',
    productions: 'S -> A\nS -> B\nA -> x\nB -> x',
  });
  assert.equal(a.conflictFree, false);
  const c = a.firstConflict;
  assert.equal(c.type, 'reduce-reduce');
  assert.equal(c.lookahead, '$');
  assert.deepEqual(c.actions.map((x) => x.type), ['reduce', 'reduce']);
  // stable order: smaller production index first
  assert.ok(c.actions[0].production < c.actions[1].production);
  assert.ok(c.actions[0].productionText.includes('A -> x'));
  assert.ok(c.actions[1].productionText.includes('B -> x'));
  // prefix evidence: reading x from state 0 lands in the conflict state
  let s = 0;
  for (const sym of c.prefix.symbols) s = a.states[s].transitions[sym];
  assert.equal(s, c.state);
});

test('state numbering is stable across repeated constructions', () => {
  const spec = {
    terminals: 'id + * ( )',
    nonterminals: 'E T F',
    start: 'E',
    productions: 'E -> E + T\nE -> T\nT -> T * F\nT -> F\nF -> ( E )\nF -> id',
  };
  const a1 = build(spec);
  const a2 = build(spec);
  const sig = (a) =>
    a.states
      .map((s) => s.items.map((i) => i.text).sort().join('&'))
      .join('||');
  assert.equal(sig(a1), sig(a2));
});

test('canonical LR(1) resolves an SLR false conflict via lookaheads (S -> L = R | R)', () => {
  // The classic Dragon-book grammar: SLR reports a shift/reduce conflict on
  // '=' but canonical LR(1) does not, because the reduce item R -> L . in the
  // relevant state does not carry '=' as a lookahead.
  const a = build({
    terminals: '= * id',
    nonterminals: 'S L R',
    start: 'S',
    productions: 'S -> L = R\nS -> R\nL -> * R\nL -> id\nR -> L',
  });
  assert.equal(a.conflictFree, true);
  assert.equal(a.conflictCount, 0);
  assert.equal(a.states.length, 14);
});

test('goto table drives consistent transitions', () => {  const a = build({
    terminals: 'a b',
    nonterminals: 'S A',
    start: 'S',
    productions: 'S -> A a\nA -> b',
  });
  for (const row of a.actionTable) {
    for (const [sym, target] of Object.entries(row.gotos)) {
      assert.ok(a.nonterminals.includes(sym));
      assert.equal(a.states[row.state].transitions[sym], target);
    }
  }
});
