namespace OptimisedGroversAlgorithm {
    // Title: Using a Generalised Algorithm to Illustrate the Complexity of Quantum Search
	// Author: Nicholas Dale
	// Version: 1.0
	// Date: 25/10/22
	// Description: This source code file includes a Q# implementation of Grover's Algorithm, along with two implemented Oracles

    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Arrays;
    open Microsoft.Quantum.Diagnostics;
    open Microsoft.Quantum.Measurement;
    open Microsoft.Quantum.Math;

    @EntryPoint()
    operation RunGrovers() : Unit {
        Message("Running Grover's Alg to solve a graph colouring problem");
        SolveGraphColouringProblems();

        Message("Running Grover's Alg to solve a Boolean Satisfiability Problem");
        SolveSATProblems();

        Message("Finished run");
    }

    // ------------------------------------------------------ //
    // Top level test sets //
    operation SolveGraphColouringProblems() : Unit { 
        // 5 Vertex 7 Edge graph
        RunGroverOnOneGraphColouring(5, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3), (3, 4)], 72);
    }

    operation SolveSATProblems() : Unit {
        // AND based SAT problem
        RunGroverOnOneSAT(2, [[(0, true), (1, true)], [(1, false), (0, false)]]);
    }

    // ------------------------------------------------------ //
    // Oracle instantiation, and calling relevant Grover loop

    // Run algorithm on one instance of the SAT problem and check that the answer is correct
    operation RunGroverOnOneSAT (nVar : Int, problem : (Int, Bool)[][]) : Unit {
        let oracle = Oracle_SAT_Reference(_, _, problem);
        let answer = RunGroverNoIterations(nVar, oracle);
        if (not F_SAT(answer, problem)) {
            fail $"Incorrect answer {answer} for {problem}";
        }
        Message($"Answer: {answer}");
    }

    operation RunGroverOnOneGraphColouring (nVertices : Int, edges : (Int, Int)[], nSolutions : Int) : Unit {
        // Define our oracle for the problem
        // There's a lot of partial application functional programming
        // techniques going on here. 
        let markingOracle = MarkValidVertexColoring(edges, _, _);

        // Define Grover's search parameters
        // We need to define 2 bits of classical info for each colour
        // since there's four colours. 
        // hence the bitstring is 10bits long. 2 bits for each vertex. 
        let nQubits = 2 * nVertices;

        // The search space is all bit strings of length nQubits. 
        let searchSpaceSize = 2 ^ (nQubits);

        // Now we have a value for N and M, we can compute the optimal # of iterations
        let nIterations = Round(PI() / 4.0 * Sqrt(IntAsDouble(searchSpaceSize) / IntAsDouble(nSolutions)));

        let answer = RunGroverIterations(nQubits, markingOracle, nIterations);

        if (not Check_Graph(answer, nVertices, edges)) {
            fail $"Incorrect answer {answer} for graph colouring}";
        }

    }

    // ------------------------------------------------------ //
    // Loops to call Grover's until correct. One generates iterations dynamically //
    operation RunGroverNoIterations (nQubits : Int, markingOracle : ((Qubit[], Qubit) => Unit is Adj)) : Bool[] {

        mutable answer = [false, size=nQubits];
        use (register, output) = (Qubit[nQubits], Qubit());
        mutable isCorrect = false; 
        let phaseOracle = ApplyMarkingOracleAsPhaseOracle(markingOracle, _);

        mutable nIterations = 1;

        repeat {
            Message($"Trying the search with {nIterations} iterations");
            RunGroversSearch(register, phaseOracle, nIterations);
            // Measure each register in our superposition, 
            // hopefully the result we want will have the highest amplitude out of the many many possible results
            let res = MultiM(register);
            // check whether result is correct
            // apply oracle to the register plus
            // ancillary bit after measurement
            markingOracle(register, output);
            if (MResetZ(output) == One) {
                set isCorrect = true; 
                set answer = ResultArrayAsBoolArray(res);
            }
            ResetAll(register);
        }
        until (isCorrect or nIterations > 100)
        fixup {
            set nIterations *= 2;
        }
        if (not isCorrect) {
            fail "Failed to satisfy the expression";
        }

        return answer;
    }

    // ------------------------------------------------------ //
    // Loops to call Grover's based on predetermined iteration count //

    // remember that unit is essentially a null return type
    // unitary is a replacement for a return
    operation RunGroverIterations (nQubits : Int, markingOracle : ((Qubit[], Qubit) => Unit is Adj), nIterations : Int) : Bool[] {

        mutable answer = [false, size=nQubits];
        use (register, output) = (Qubit[nQubits], Qubit());
        mutable isCorrect = false; 
        let phaseOracle = ApplyMarkingOracleAsPhaseOracle(markingOracle, _);

        repeat {
            RunGroversSearch(register, phaseOracle, nIterations);
            // Measure each register in our superposition, 
            // hopefully the result we want will have the highest amplitude out of the many many possible results
            let res = MultiM(register);
            // Classically check whether the result is correct
            markingOracle(register, output);
            if (MResetZ(output) == One) {
                set isCorrect = true; 
                set answer = ResultArrayAsBoolArray(res);
            }
            ResetAll(register);
        }
        until (isCorrect);
        return answer;
        }

    // ------------------------------------------------------ //
    // Main implementations of Grover's Algorithm
    operation RunGroversSearch(register : Qubit[], phaseOracle : ((Qubit[]) => Unit is Adj), iterations : Int) : Unit {
        // Prepare equal superposition of all states
        ApplyToEach(H, register);

        // Grover's Iterations
        for _ in 1 .. iterations {
            // Apply oracle
            phaseOracle(register);
            // Amplitude amplification (reflection around mean)
            within {
                ApplyToEachA(H, register);
                ApplyToEachA(X, register);
            }
            apply {
                Controlled Z(Most(register), Tail(register));
            }
        }
    }

    // ------------------------------------------------------ //
    // Generic utility functions to run Grover's
    // Utilise Phase Kickback trick

    operation ApplyMarkingOracleAsPhaseOracle(markingOracle : ((Qubit[], Qubit) => Unit is Adj), register : Qubit[]) : Unit
    is Adj {
        use target = Qubit();
        within {
            // Put target qubit into - state
            X(target);
            H(target);
        }
        apply {
            // Apply marking oracle using phase kickback,
            // since target is in - state, flipping the target
            // will apply a -1 relative phase to register state
            markingOracle(register, target);
        }
    }

    // ------------------------------------------------------ //
    // Implementation for Graph Colouring Oracle

    operation MarkColorEquality(c0 : Qubit[], c1 : Qubit[], target : Qubit) : Unit
    is Adj + Ctl {
        // The within-apply block undoes the effect in the within block
        // automatically - implementing reversible computation
        within {
            // We have c0, and c1 representing colours of the verticies
            // we will iterate over the two arrays with Zipped to get matching pairs
            for (q0, q1) in Zipped(c0, c1) {
                // We use the Controlled not gate to store the equality in q1
                CNOT(q0,q1);
            }
        }
        apply {
            // If the qubit strings are equal, i.e. each element in q1 is 0
            // (since xor 0,0 or 1,1 == 0), we flip the state of the target
            (ControlledOnInt(0,X))(c1, target);
        }
    }

    operation MarkValidVertexColoring(edges : (Int, Int)[], colorsRegister : Qubit[], target : Qubit) : Unit
    is Adj + Ctl {
        let nEdges = Length(edges);
        // split our quantum regiser into array of two-qubit registers
        let colors = Chunks(2, colorsRegister);
        // Allocate an ancillery qubit for each edge to mark the edges that connect vertices with the same colour. 
        use conflictQubits = Qubit[nEdges];
        within {
            for ((start, end), conflictQubit) in Zipped(edges, conflictQubits) {
                // Check that the verticies of each edge have different colours using MarkColorEquality operation
                MarkColorEquality(colors[start], colors[end], conflictQubit);
            }
        }
        apply {
            // If there are no conflicts, don't flip the target. 
            // If there are, store result in target. 
            // This syntax is like defining a function, and then calling it. 
            (ControlledOnInt(0,X))(conflictQubits, target);
        }
    }

    // ------------------------------------------------------ //
    // Hash function Oracles
    // TODO

    // ------------------------------------------------------ //
    // SAT Oracles
    // Solves the General SAT problem
    // Find values that satisfy
    // f(x) = ∧ᵢ (∨ₖ yᵢₖ), yᵢₖ = either xᵢₖ or ¬xᵢₖ
    operation Oracle_SAT_Reference (queryRegister : Qubit[], 
                    target : Qubit, 
                    problem : (Int, Bool)[]
                    []) : Unit is Adj {
        // Allocate Qubits to store results of clause evaluation
        use ancillaRegister = Qubit[Length(problem)];
        // Compute clauses, evaluate the overall formula as an AND oracle
        within {
            EvaluateOrClauses(queryRegister, ancillaRegister, problem, Oracle_SATClause_Reference);
        } apply {
            Controlled X (ancillaRegister, target);
        }
    }

    // Evaluate all OR clauses in the formula
    operation EvaluateOrClauses (queryRegister : Qubit[], 
                                ancillaRegister : Qubit[], 
                                problem : (Int, Bool)[][], 
                                clauseOracle : ((Qubit[], Qubit, (Int, Bool)[]) => Unit is Adj)) : Unit is Adj {
        for clauseIndex in 0 .. Length (problem)-1 {
            clauseOracle(queryRegister, ancillaRegister[clauseIndex], problem[clauseIndex]);
        }
    }

    // Evaluate one caluse of SAT formula
    operation Oracle_SATClause_Reference (queryRegister : Qubit[],
                                target : Qubit, 
                                clause : (Int, Bool)[]) : Unit is Adj {
        let (clauseQubits, flip) = GetClauseQubits(queryRegister, clause);

        // Calculate the clause
        within {
            ApplyPauliFromBitString(PauliX, true, flip, clauseQubits);
        } apply {
            Oracle_Or_Reference(clauseQubits, target);
        }
    }

    // Note how this is a function not an operation
    // It has a return value
    // Functions are used for composability and reusable code here
    function GetClauseQubits (queryRegister : Qubit[], clause : (Int, Bool)[]) : (Qubit[], Bool[]) {
        mutable clauseQubits = [];
        mutable flip = [];
        // using foreach tuple syntax
        for (index, isTrue) in clause {
            // Add the variable from the caluse into the list of variables
            // needed to call OR oracle
            set clauseQubits += [queryRegister[index]];
            // If the variable is negated in the formula, 
            // mark the qubit as needing a flip
            set flip += [not isTrue];
        }

        return (clauseQubits, flip);
    }

    function Check_Graph (graphColouring : Bool[], nVertices : Int, edges : (Int, Int)[]) : Bool {
        let colourBits = Chunks(2, graphColouring);

        Message("The resulting graph colouring: ");
        for i in 0 .. nVertices - 1 {
            Message($"Vertex {i} - colour {BoolArrayAsInt(colourBits[i])}");
        }
        // Bit of a lazy brute force algorithm
        // For each vertex
        for v in 0 .. nVertices - 1 {

            Message("Validating graph colouring: ");
            Message($"Vertex {v} - colour {BoolArrayAsInt(colourBits[v])}");

            // For each edge
            for e in 0 .. Length(edges) - 1 {
                // Check if the edge connects to the vertex
                let (start, end) = edges[e];
                if start == v {
                    // If the edge connects, find the other vertex
                    let start_colour = BoolArrayAsInt(colourBits[start]);
                    let end_colour = BoolArrayAsInt(colourBits[end]);
                // Compare the two colours
                // If they are equal, fail immediately
                    if start_colour == end_colour {
                        return false;
                    }
                // Otherwise, loop
                }
            }
        }

        return true;

    }

    // ------------------------------------------------------ //
    // SAT Testing Functions
    // The code below was copied from https://github.com/microsoft/QuantumKatas - SolveSATWithGrover
    // In accordance with the provided MIT License
    function F_SAT (args : Bool[], problem : (Int, Bool)[][]) : Bool {
        for clause in problem {
            // One clause can invalidate the whole formula
            if (not F_SATClause(args, clause)) {
                return false;
            }
        }
        return true;
    }

    // Evaluate one clause of the SAT formula
    function F_SATClause (args : Bool[], clause : (Int, Bool)[]) : Bool {
        for (index, isTrue) in clause {
            if (isTrue == args[index]) {
                // one true literal is sufficient for the clause to be true
                return true;
            }
        }
        // none of the literals is true - the whole clause is false
        return false;
    }
    
    // AND oracle for an arbitrary number of qubits in query register
    operation Oracle_And_Reference (queryRegister : Qubit[], target : Qubit) : Unit is Adj {        
        Controlled X(queryRegister, target);
    }

    // OR oracle for an arbitrary number of qubits in query register
    operation Oracle_Or_Reference (queryRegister : Qubit[], target : Qubit) : Unit is Adj {        
        // x₀ ∨ x₁ = ¬ (¬x₀ ∧ ¬x₁)
        // First, flip target if both qubits are in |0⟩ state
        (ControlledOnInt(0, X))(queryRegister, target);
        // Then flip target again to get negation
        X(target);
    }




    // ------------------------------------------------------ //
    // Alternating Bits oracle
    // The code below was copied from https://github.com/microsoft/QuantumKatas - SolveSATWithGrover
    // In accordance with the provided MIT License

    // Answer-based solution for alternating bits oracle
    // Alternating bits oracle: f(x) = (x₀ ⊕ x₁) ∧ (x₁ ⊕ x₂) ∧ ... ∧ (xₙ₋₂ ⊕ xₙ₋₁)
    operation Oracle_AlternatingBits_Reference (queryRegister : Qubit[], target : Qubit) : Unit is Adj {
        
        // Allocate N-1 qubits to store results of clauses evaluation
        let N = Length(queryRegister);
        use anc = Qubit[N-1];
        within {
            // Evaluate all XOR clauses (using XOR oracle) and uncompute after
            for i in 0..N-2 {
                Oracle_Xor_Reference(queryRegister[i..i+1], anc[i]);
            }
        }
        apply {
            // Evaluate the overall formula as an AND oracle (can use reference depending on the implementation)
            Controlled X(anc, target);
        }
    }

    operation FlipAlternatingPositionBits_Reference (register : Qubit[], firstIndex : Int) : Unit is Adj {
        
        // iterate over elements in every second position, starting with firstIndex (indexes are 0-based)
        for i in firstIndex .. 2 .. Length(register) - 1 {
            X(register[i]);
        }
    }

    operation Oracle_AlternatingBits_Answer (queryRegister : Qubit[], target : Qubit) : Unit is Adj {
        
        // similar to task 1.2 from GroversAlgorithm kata: 
        // first mark the state with 1s in even positions (starting with the first qubit, index 0), 
        // then mark the state with 1s in odd positions
        for firstIndex in 0..1 {
            within {
                FlipAlternatingPositionBits_Reference(queryRegister, firstIndex);
            } 
            apply {
               Controlled X(queryRegister, target);
            }
        }
    }

    // XOR oracle for an arbitrary number of qubits in query register
    operation Oracle_Xor_Reference (queryRegister : Qubit[], target : Qubit) : Unit is Adj {        
        ApplyToEachA(CNOT(_, target), queryRegister);
    }

}


