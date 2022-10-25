namespace OptimisedGroversAlgorithm {
    open Microsoft.Quantum.Arrays;
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Diagnostics;
    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Math;
    open Microsoft.Quantum.Random;

    // Test 1 of 2, for SAT
    @Test("QuantumSimulator")
    operation T11_UniversalGroversAlgorithm () : Unit {
        // AND: 1 solution/4
        RunGroverOnOneSAT(2, [[(0, true)], [(1, true)]]);

        // XOR: 2 solutions/4
        RunGroverOnOneSAT(2, [[(0, true), (1, true)], [(1, false), (0, false)]]);

        // OR: 3 solutions/4
        RunGroverOnOneSAT(2, [[(0, true), (1, true)]]);

        // Alternating bits: 2 solutions/2^4
        RunGroverOnOneSAT(4, [[(1, false), (2, false)], [(0, true), (1, true)], [(1, false), (0, false)], [(2, true), (1, true)], [(2, false), (3, false)], [(3, true), (2, true)]]);

        // SAT instance: 1/2^6
        RunGroverOnOneSAT(6, [[(1, false)], [(0, true), (1, true)], [(2, true), (3, true), (4, true)], [(3, false), (5, false)], [(0, false), (2, false), (5, true)], [(1, true), (3, true), (4, false)], [(1, true), (5, true)]]);
    }
    // TODO
    // Test 2 of 2 for Graph Colouring
    @Test("QuantumSimulator")
    operation T21_UniversalGroversAlgorithm () : Unit {

        RunGroverOnOneGraphColouring(5, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3), (3, 4)], 72);

    }

    // Test the Check_Graph function
    @Test("QuantumSimulator")
    operation T22_UniversalGroversAlgorithm () : Unit {
        let validColouring = [false, false, true, false, false, true, true, true, true, false];
        let invalidColouring = [false, false, true, false, false, true, true, true, true, true];
        let edges = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3), (3, 4)];
        let nVertices = 5;

        let true_case = Check_Graph(validColouring, nVertices, edges);

        if (not true_case) {
            fail $"Incorrect answer {true_case} for Graph Colouring";
        }

        let false_case = Check_Graph(invalidColouring, nVertices, edges);

        if (false_case) {
            fail $"Incorrect answer {false_case} for Graph Colouring";
        }

    }

}
