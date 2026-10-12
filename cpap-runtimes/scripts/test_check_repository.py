"""Tests for the source rules and the cited-hypothesis check of the repository check."""
import unittest

from check_repository import ALMOST_LINEAR, A2SAT, FLOW, FORBIDDEN, FPT, hypothesis_problems
from generate_challenge import without_comments


class ForbiddenTests(unittest.TestCase):
    def test_forbidden_constructs(self):
        for code in ['theorem t : 1 = 1 := by native_decide', 'axiom bad : False',
                     'private axiom bad : False', '@[implemented_by f] def g := 0',
                     '@[extern "c_fn"] opaque h : Nat', 'unsafe def u : Nat := 0',
                     'set_option maxHeartbeats 0 in', 'set_option debug.skipKernelTC true',
                     'theorem t : True := by admit']:
            self.assertIsNotNone(FORBIDDEN.search(code), code)

    def test_allowed_constructs(self):
        for code in ['theorem t : 1 = 1 := by decide +kernel', 'set_option maxHeartbeats 400000 in',
                     'theorem axiom_free : True := trivial', 'def externalNodes : Nat := 0',
                     '/-- `native_decide` is not used. -/ theorem t : True := trivial',
                     'meta import Runtimes.ZeroCost']:
            self.assertIsNone(FORBIDDEN.search(without_comments(code)), code)


def binders(name: str) -> str:
    """The hypotheses of a compared theorem of the expected shape."""
    primed = name.endswith('ram_all') or name.endswith('ram_all_almostLinear')
    parts = []
    if name in FLOW:
        parts.append('(hF : MinCostFlowSolver F T)')
    if name in ALMOST_LINEAR:
        parts.append('(hT : AlmostLinear T)')
    if name in A2SAT:
        parts.append("(hA : Almost2SatSolver F' T')" if primed else '(hA : Almost2SatSolver F T)')
    if name in FPT:
        parts.append("(hT' : FPTBound T')" if primed else '(hT : FPTBound T)')
    return ' '.join(parts)


def statements() -> dict[str, str]:
    """Statements of the hypothesis-taking targets, of the expected shape."""
    result = {}
    for name in sorted(FLOW | A2SAT):
        short = name.split('.')[-1]
        result[name] = (f'/-- With the cited hypotheses (`MinCostFlowSolver`). -/\n'
                        f'theorem {short} {binders(name)} :\n    True := by sorry')
    return result


class HypothesisTests(unittest.TestCase):
    def test_expected_shape(self):
        ok = dict(statements(), **{
            'Runtimes.ZeroCost.zeroCost_ram': '/-- No flow (`MinCostFlowSolver`). -/\n'
                                              'theorem zeroCost_ram : True := by sorry'})
        self.assertEqual(hypothesis_problems(ok), [])

    def test_hypothesis_outside_its_targets(self):
        bad = dict(statements(), **{
            'Runtimes.ZeroCost.zeroCost_ram':
                'theorem zeroCost_ram (hF : MinCostFlowSolver F T) : True := by sorry'})
        self.assertEqual(len(hypothesis_problems(bad)), 1)
        name = 'Runtimes.Flow.cpap4_flow_single'
        a2 = dict(statements(), **{
            name: 'theorem cpap4_flow_single (hF : MinCostFlowSolver F T) (hA : Almost2SatSolver F T) : '
                  'True := by sorry'})
        self.assertEqual(len(hypothesis_problems(a2)), 1)

    def test_missing_or_hidden_hypothesis(self):
        name = 'Runtimes.Flow.cpap4_flow_single'
        hidden = dict(statements(), **{
            name: 'theorem cpap4_flow_single : ∀ F T, MinCostFlowSolver F T → True := by sorry'})
        self.assertEqual(len(hypothesis_problems(hidden)), 1)
        missing = statements()
        del missing[name]
        self.assertEqual(len(hypothesis_problems(missing)), 1)
        name = 'Runtimes.BoundedCost.boundedCost_ram_fpt'
        lacking = dict(statements(), **{
            name: 'theorem boundedCost_ram_fpt (hA : Almost2SatSolver F T) : True := by sorry'})
        self.assertEqual(len(hypothesis_problems(lacking)), 1)

    def test_almost_linear_where_expected(self):
        name = 'Runtimes.Flow.cpap4_flow_single'
        extra = dict(statements(), **{
            name: 'theorem cpap4_flow_single (hF : MinCostFlowSolver F T) (hT : AlmostLinear T) : '
                  'True := by sorry'})
        self.assertEqual(len(hypothesis_problems(extra)), 1)
        name = 'Runtimes.cpap4_enum_ram_semantic'
        lacking = dict(statements(), **{
            name: 'theorem cpap4_enum_ram_semantic (hF : MinCostFlowSolver F T) : True := by sorry'})
        self.assertEqual(len(hypothesis_problems(lacking)), 1)


if __name__ == '__main__':
    unittest.main()
