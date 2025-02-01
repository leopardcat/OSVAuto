"""Unit test for model construction"""

import unittest

from osverify import os_struct
from osverify.os_struct import Int32U, Int, MapType, SeqType
from osverify import os_term
from osverify.os_term import int32u, integer
from osverify import os_parser
from osverify import os_model
from osverify.os_theory import OSTheory
from osverify import os_z3wrapper
from osverify.os_model import base_key, ModelKey, UnknownTerm, FullTerm, PartialMapTerm, \
    PartialSeqTerm, PartialStructTerm, PartialFunTerm
from osverify.os_z3wrapper import UnsatResult, ModelResult
from osverify.os_proofstate import ProofState

def basic_thy() -> OSTheory:
    return os_parser.load_theory("basic", verbose=False)


class ModelTest(unittest.TestCase):
    def solve_model(self, thy: OSTheory, state: ProofState, *,
                    verbose: bool = False,
                    vars: dict[str, str] = None,
                    print_vars: bool = False) -> os_model.Model:
        """Solve a list of constraints for a model.

        This function also tests that the resulting model satisfies all
        constraints.

        Parameters
        ----------
        thy: OSTheory
            the current theory
        state: ProofState
            proof state to solve model
        verbose: bool, default to False
            print additional information during test
        vars: dict[str, str], default to None
            mapping from variable name to expected value
        print_vars: bool, default to False
            whether to print models for variables

        """
        define_eqs, assumes, concl = os_z3wrapper.simplify_state(thy, state)
        res = os_z3wrapper.solve_impl(thy, assumes, concl)
        if isinstance(res, UnsatResult):
            raise AssertionError("solve_model: constraints are unsatisfiable")
        elif isinstance(res, ModelResult):
            if verbose:
                print("--- Z3 model ---")
                print(res.z3_model)
            model = os_model.convert_model_on_state(
                thy, state, res.z3_model, verbose=verbose, check_model=True)
            
            # First-stage converted model, before filling by defining equations
            if verbose:
                print("--- Converted model ---")
                print(model)
            if verbose:
                print("--- Defining equations ---")
                for eq in define_eqs:
                    print(eq)

            # Check variables
            if vars:
                for name, expected_val in vars.items():
                    pt = model.var_data[name]
                    self.assertEqual(str(pt), expected_val)

            # Print variables
            if print_vars:
                for name in state.fixes_map:
                    print(name + ": " + str(model.var_data[name]))
            return model
        else:
            raise NotImplementedError
        
    def testGetSuffix(self):
        key = ModelKey("q.m1", [])
        key2 = key.get_suffix(ModelKey("q", []))
        self.assertEqual(key2, ModelKey(".m1", []))

    def testPartialTermUpdateUnknown(self):
        thy = basic_thy()
        t = UnknownTerm(type=Int32U)
        t2 = t.update(thy, base_key, FullTerm(int32u(3)))
        self.assertEqual(t2, FullTerm(int32u(3)))

    def testPartialTermUpdateUnknownGet(self):
        thy = basic_thy()
        ty = MapType(Int32U, Int32U)
        t = UnknownTerm(type=ty)
        t2 = t.update(thy, ModelKey(".get", [int32u(3)]), FullTerm(int32u(5)))
        self.assertEqual(t2, PartialMapTerm({int32u(3): FullTerm(int32u(5))},
                                            dict(), type=ty))

    def testPartialTermUpdateUnknownIndom(self):
        thy = basic_thy()
        ty = MapType(Int32U, Int32U)
        t = UnknownTerm(type=ty)
        t2 = t.update(thy, ModelKey(".indom", [int32u(3)]), FullTerm(os_term.OSNumber(True)))
        self.assertEqual(t2, PartialMapTerm(dict(),
                                            {int32u(3): FullTerm(os_term.OSNumber(True))}, type=ty))

    def testPartialTermUpdateUnknownIndex(self):
        thy = basic_thy()
        ty = SeqType(Int32U)
        t = UnknownTerm(type=ty)
        t2 = t.update(thy, ModelKey(".index", [integer(3)]), FullTerm(int32u(5)))
        self.assertEqual(t2, PartialSeqTerm({3: FullTerm(int32u(5))},
                                            UnknownTerm(type=Int),
                                            type=ty))

    def testPartialTermUpdateUnknownStruct(self):
        thy = basic_thy()

        struct = """
        struct Point {
            int32u x;
            int32u y;
        }
        """
        thy.add_struct(os_parser.parse_struct(thy, struct))

        t = UnknownTerm(type=os_struct.OSStructType("Point"))
        t2 = t.update(thy, ModelKey(".x", []), FullTerm(int32u(3)))
        self.assertEqual(t2, PartialStructTerm("Point", [("x", FullTerm(int32u(3)))]))

    def testPartialTermUpdateMap(self):
        thy = basic_thy()
        ty = MapType(Int32U, Int32U)
        t = PartialMapTerm({int32u(3): FullTerm(int32u(5))}, {}, type=ty)
        t2 = t.update(thy, ModelKey(".get", [int32u(5)]), FullTerm(int32u(8)))
        self.assertEqual(t2, PartialMapTerm({int32u(3): FullTerm(int32u(5)),
                                             int32u(5): FullTerm(int32u(8))},
                                            {}, type=ty))

    def testPartialTermUpdateSeqIndex(self):
        thy = basic_thy()
        ty = SeqType(Int32U)
        t = PartialSeqTerm({3: FullTerm(int32u(5))}, UnknownTerm(type=Int), type=ty)
        t2 = t.update(thy, ModelKey(".index", [integer(5)]), FullTerm(int32u(8)))
        self.assertEqual(t2, PartialSeqTerm({3: FullTerm(int32u(5)),
                                             5: FullTerm(int32u(8))},
                                             UnknownTerm(type=Int),
                                             type=ty))

    def testPartialTermUpdateSeqLength(self):
        thy = basic_thy()
        ty = SeqType(Int32U)
        t = PartialSeqTerm({3: FullTerm(int32u(5))}, UnknownTerm(type=Int), type=ty)
        t2 = t.update(thy, ModelKey(".length", []), FullTerm(integer(7)))
        self.assertEqual(t2, PartialSeqTerm({3: FullTerm(int32u(5))},
                                             FullTerm(integer(7)),
                                             type=ty))

    def testPartialTermUpdateStruct(self):
        thy = basic_thy()

        struct = """
        struct Point {
            int32u x;
            int32u y;
        }
        """
        thy.add_struct(os_parser.parse_struct(thy, struct))

        t = PartialStructTerm("Point", [("x", FullTerm(int32u(3)))])
        t2 = t.update(thy, ModelKey(".y", []), FullTerm(int32u(5)))
        self.assertEqual(t2, PartialStructTerm("Point", [("x", FullTerm(int32u(3))),
                                                         ("y", FullTerm(int32u(5)))]))

    def testVar(self):
        thy = basic_thy()

        state = """state {
            fixes i : int32u;
            fixes j : int32u;
            assumes i == 32 && j == 64;
            shows false
        }
        """
        state = os_parser.parse_proof_state(thy, state)
        self.solve_model(thy, state, vars={"i": "32", "j": "64"})

    def testSeq(self):
        thy = basic_thy()

        state = """state {
            fixes a: Seq<int32u>;
            assumes |a| == 2 && a[0] == 1 && a[1] == 2;
            shows false
        }
        """
        state = os_parser.parse_proof_state(thy, state)
        self.solve_model(thy, state, vars={"a": "[0: 1, 1: 2, len=2]"})

    def testMap(self):
        thy = basic_thy()

        state = """state {
            fixes m: Map<int32u, int32u>;
            assumes indom(1, m) && indom(2, m) && indom(3, m);
            assumes get(1, m) == 1 && get(2, m) == 4 && get(3, m) == 9;
            shows false
        }
        """
        state = os_parser.parse_proof_state(thy, state)
        self.solve_model(thy, state, vars={"m": "{1: 1, 2: 4, 3: 9}"})

    def testMapStruct(self):
        # Test when value of map is struct
        thy = basic_thy()

        struct = """
        struct Point {
            int32u x;
            int32u y;
        }
        """
        thy.add_struct(os_parser.parse_struct(thy, struct))

        state = """state {
            fixes m: Map<int32u, Point>;
            assumes indom(0, m) && get(0, m).x == 0 && get(0, m).y == 1;
            assumes indom(1, m) && get(1, m).x == 2 && get(1, m).y == 3;
            shows false
        }
        """
        state = os_parser.parse_proof_state(thy, state)
        self.solve_model(thy, state, vars={"m": "{0: Point{{x: 0, y: 1}}, 1: Point{{x: 2, y: 3}}}"})

    def testStructMap(self):
        # Test when field of struct is map
        thy = basic_thy()

        struct = """
        struct Global {
            Map<int32u, int32u> m1;
            Map<int32u, int32u> m2;
        }
        """
        thy.add_struct(os_parser.parse_struct(thy, struct))

        state = """state {
            fixes global: Global;
            assumes indom(0, global.m1) && get(0, global.m1) == 2;
            assumes indom(1, global.m2) && get(1, global.m2) == 3;
            shows false
        }"""
        state = os_parser.parse_proof_state(thy, state)
        self.solve_model(thy, state, vars={"global": "Global{{m1: {0: 2}, m2: {1: 3}}}"})
 
    def testStruct(self):
        thy = basic_thy()

        struct = """
        struct Point {
            int32u x;
            int32u y;
        }
        """
        thy.add_struct(os_parser.parse_struct(thy, struct))

        state = """state {
            fixes p: Point;
            fixes q: Point;
            assumes p.x == 2 && p.y == 3 && q.x == 4 && q.y == 5;
            shows false
        }
        """
        state = os_parser.parse_proof_state(thy, state)
        self.solve_model(
            thy, state,
            vars={"p": "Point{{x: 2, y: 3}}", "q": "Point{{x: 4, y: 5}}"})

    def testDatatype(self):
        thy = basic_thy()

        datatype = """
        datatype Point =
            PointA(int32u x, int32u y)
          | PointB(int32u x, int32u z)
        """
        thy.add_datatype(os_parser.parse_datatype(thy, datatype))

        state = """state {
            fixes v: Point;
            fixes w: Point;
            assumes v.id == 0 && v.x == 2 && v.y == 3;
            assumes w.id == 1 && w.x == 4 && w.z == 5;
            shows false
        }
        """
        state = os_parser.parse_proof_state(thy, state)
        self.solve_model(
            thy, state,
            vars={"v": "PointA(2, 3)", "w": "PointB(4, 5)"})

    def testNestedSequence(self):
        thy = basic_thy()

        state = """state {
            fixes a: Seq<Seq<int32u> >;
            assumes |a| == 1;
            assumes |a[0]| == 1;
            assumes a[0][0] == 2;
            shows false
        }"""
        state = os_parser.parse_proof_state(thy, state)
        self.solve_model(thy, state, vars={"a": "[0: [0: 2, len=1], len=1]"})

    def testSeqNoLength(self):
        thy = basic_thy()

        state = """state {
            fixes a: Seq<int32u>;
            assumes a[3] == 2;
            assumes a[5] == 3;
            shows false
        }"""
        state = os_parser.parse_proof_state(thy, state)
        self.solve_model(thy, state, vars={"a": "[3: 2, 5: 3, len=?]"})

    def testMapUpdate(self):
        thy = basic_thy()

        state = """state {
            fixes a: Map<int32u, int32u>;
            fixes b: Map<int32u, int32u>;
            assumes b == updateMap(3, 5, a);
            assumes get(2, a) == 3;
            shows false
        }"""
        state = os_parser.parse_proof_state(thy, state)
        self.solve_model(
            thy, state,
            vars = {"a": "{2: 3}",
                    "b": "{2: 3, 3: 5}"})

    def testMapUpdate2(self):
        thy = basic_thy()

        state = """state {
            fixes a: Map<int32u, int32u>;
            fixes b: Map<int32u, int32u>;
            assumes b == updateMap(3, 5, a);
            assumes get(2, a) == 3;
            assumes get(3, a) == 4;
            assumes get(4, b) == get(3, b) + 1;
            shows false
        }"""
        state = os_parser.parse_proof_state(thy, state)
        self.solve_model(
            thy, state,
            vars = {"a": "{2: 3, 3: 4, 4: 6}",
                    "b": "{2: 3, 3: 5, 4: 6}"})

    def testMapUpdate3(self):
        thy = basic_thy()

        state = """state {
            fixes a: Map<int32u, int32u>;
            fixes b: Map<int32u, int32u>;
            fixes c: Map<int32u, int32u>;
            assumes b == updateMap(3, 5, a);
            assumes c == updateMap(4, 6, b);
            assumes get(2, c) == 3;
            shows false
        }"""
        state = os_parser.parse_proof_state(thy, state)
        self.solve_model(
            thy, state,
            vars = {"a": "{2: 3}",
                    "b": "{2: 3, 3: 5}",
                    "c": "{2: 3, 3: 5, 4: 6}"})

    def testStructUpdate(self):
        thy = basic_thy()

        struct = """
        struct Point {
            int32u x;
            int32u y;
        }
        """
        thy.add_struct(os_parser.parse_struct(thy, struct))

        state = """state {
            fixes p: Point;
            fixes q: Point;
            assumes q == p{y := 3};
            assumes q.x == 2;
            assumes p.y == 5;
            shows false
        }"""
        state = os_parser.parse_proof_state(thy, state)
        self.solve_model(
            thy, state,
            vars = {"p": "Point{{x: 2, y: 5}}",
                    "q": "Point{{x: 2, y: 3}}"})

    def testStructUpdateMap(self):
        thy = basic_thy()

        struct = """
        struct MapPair {
            Map<int32u, int32u> m1;
            Map<int32u, int32u> m2;
        }
        """
        thy.add_struct(os_parser.parse_struct(thy, struct))

        state = """state {
            fixes p: MapPair;
            fixes q: MapPair;
            assumes p.m1 == updateMap(1, 2, p.m2);
            assumes q.m1 == updateMap(2, 4, q.m2);
            assumes p.m2 == updateMap(3, 6, q.m1);
            assumes get(4, p.m1) == 8;
            shows false
        }"""
        state = os_parser.parse_proof_state(thy, state)
        self.solve_model(
            thy, state,
            vars = {"p": "MapPair{{m1: {1: 2, 2: 4, 3: 6, 4: 8}, m2: {2: 4, 3: 6, 4: 8}}}",
                    "q": "MapPair{{m1: {2: 4, 4: 8}, m2: {4: 8}}}"})

    def testMultipleEqs(self):
        thy = basic_thy()

        state = """state {
            fixes a: Map<int32u, int32u>;
            fixes b: Map<int32u, int32u>;
            fixes c: Map<int32u, int32u>;
            assumes a == b;
            assumes b == c;
            assumes get(0, a) == 1;
            shows false
        }"""
        state = os_parser.parse_proof_state(thy, state)
        self.solve_model(thy, state, vars = {"a": "{0: 1}", "b": "{0: 1}", "c": "{0: 1}"})

    def testStructEq(self):
        thy = basic_thy()

        struct = """
        struct Point {
            int32u x;
            int32u y;
        }
        """
        thy.add_struct(os_parser.parse_struct(thy, struct))

        state = """state {
            fixes p: Point;
            fixes q: Point;
            assumes p == Point{{x: 3, y: 5}};
            assumes q{x := 3} == p{y := 6};
            assumes q{y := 5} == p{x := 2};
            shows false
        }"""
        state = os_parser.parse_proof_state(thy, state)
        self.solve_model(thy, state, vars = {"p": "Point{{x: 3, y: 5}}",
                                             "q": "Point{{x: 2, y: 6}}"})

    def testDatatypeEq(self):
        thy = basic_thy()

        datatype = """
        datatype Point =
            PointA(int32u x, int32u y)
          | PointB(int32u x, int32u z)
        """
        thy.add_datatype(os_parser.parse_datatype(thy, datatype))

        state = """state {
            fixes p: Point;
            assumes PointA(3, 5) == p;
            shows false
        }"""
        state = os_parser.parse_proof_state(thy, state)
        self.solve_model(thy, state, vars = {"p": "PointA(3, 5)"})

    def testSeqAppend(self):
        thy = basic_thy()

        state = """state {
            fixes a: Seq<int32u>;
            fixes b: Seq<int32u>;
            fixes c: Seq<int32u>;
            assumes a == b ++ c;
            assumes |b| == 3;
            assumes |c| == 4;
            assumes b[0] == 1;
            assumes c[0] == 1;
            shows false
        }
        """
        state = os_parser.parse_proof_state(thy, state)
        self.solve_model(thy, state, vars = {"a": "[0: 1, 3: 1, len=7]",
                                             "b": "[0: 1, len=3]",
                                             "c": "[0: 1, len=4]"})

    def testAxiomFunc(self):
        thy = basic_thy()

        os_parser.parse_theory_items(
            thy, """
            axiomfunc P: int32u -> bool
            """
        )

        state = """state {
            fixes a: int32u;
            assumes a == 1;
            shows P(a)
        }"""
        state = os_parser.parse_proof_state(thy, state)
        self.solve_model(thy, state, vars = {"a": "1"})

    def testIndom(self):
        thy = basic_thy()

        state = """state {
            fixes m: Map<int, int>;
            assumes indom(2, m);
            assumes !indom(3, m);
            assumes get(2, m) == 4;
            shows false
        }"""
        state = os_parser.parse_proof_state(thy, state)
        self.solve_model(thy, state, vars = {"m": "{2: 4, 3: -}"})


if __name__ == "__main__":
    unittest.main()
