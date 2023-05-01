namespace Collision_Problem {

    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Diagnostics;
    open Microsoft.Quantum.Math;
    open Microsoft.Quantum.Arrays;
    open Microsoft.Quantum.Measurement;
    open Microsoft.Quantum.Bitwise;
    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Random;
    open Microsoft.Quantum.Arithmetic;
    
    
    operation RandomNumberGenerator() : Result {
        // Allocate a qubit        
        use q = Qubit();  
        // Put the qubit to superposition
        // It now has a 50% chance of being measured 0 or 1  
        H(q);      
        // Measure the qubit value            
        return M(q);           
    }

    operation RandomNumberGeneratorInRange(K : Int) : Int {
        let n = Ceiling(Lg(IntAsDouble(K)));
        mutable result = -1;
        repeat {
            use qubits = Qubit[n] {
                ApplyToEach(H, qubits);
                let randomInt = MeasureInteger(LittleEndian(qubits));
                if (randomInt <= K) {
                    set result = randomInt;
                }
            }
        } until (result >= 0);
        return result;
    }

    operation GeneraterandomInt(x : Int, k : Int) : Int[] {
        mutable results = ConstantArray(k, 0);
        for i in 0 .. k - 1 {
                mutable output = 0; 
                repeat {
                    mutable bits = []; 
                    for idxBit in 1..BitSizeI(x) {
                        set bits += [RandomNumberGenerator()]; 
                    }
                    set output = ResultArrayAsInt(bits);
                } until (output <= x);
                // Add the random integer to the array
                set results w/= i <- output;
        }
        return results;
    }
    
    operation GetRandomIndex(max : Int) : Int {
        mutable output = 0; 
        repeat {
            mutable bits = []; 
            for idxBit in 1..BitSizeI(max) {
                set bits += [RandomNumberGenerator()]; 
            }
            set output = ResultArrayAsInt(bits);
        } until (output <= max);
        return output;
    }

    // Define a function to compare two tuples based on their second element
    function CompareSecond(tuple1 : (Int, Int), tuple2 : (Int, Int)) : Bool {
        let (t_1 , t_2) = tuple1;
        let (t1 , t2) = tuple2;
        if t_2 < t2 {
            return false;
        }
        else{
            return true;
        }
    }
    
    operation GroverSearch(F : ((Int, Int) -> Int), N : Int,table :Int[][]) : Int {
    // Define the size of the search space X.
        let numBits = Ceiling(Lg(IntAsDouble(N)));
        mutable result = 0;
        // Initialize the state to a uniform superposition.
        use mark = Qubit[numBits + 1];
        within {
            ApplyToEachA(H, mark);
            }apply {
                // Apply the Grover search algorithm.
                let numIterations = RandomNumberGeneratorInRange(Length(table));
                let x0 = RandomNumberGeneratorInRange(N);
                for i in 1 .. numIterations {
                    Oracle(F,mark,x0,table,N);
                    Diffusion(numBits, mark);
                }

                // Measure the state and return the result.
                set result = MeasureInteger(LittleEndian(mark[0 .. numBits - 1]));
                ResetAll(mark);
            }
        return result;
    }
    // Define a function to check if x0 is marked.
    // Returns 1 if x0 is marked, and 0 otherwise.
    function IsMarked(F : ((Int, Int) -> Int),x0 : Int,table :Int[][], n : Int) : Int {
        for i in 0 .. Length(table) - 1 {
            if (x0 != table[i][0] and F(x0, n) == table[i][1]) {
                return 1;
            }
        }
        return 0;
    }
    // Define the oracle.
    operation Oracle(F : ((Int, Int) -> Int),mark : Qubit[], x0 : Int,L :Int[][],n:Int) : Unit {
        // Apply the phase kickback to marked states.
        let phase = 1 - 2 * IsMarked(F,x0,L,n);
        if (phase == -1) {
            X(mark[0]);
        }
        use q =  Qubit[x0];
        Controlled Z(mark,q[0]);
        if (phase == -1) {
            X(mark[0]);
        }
        }
    // Define the diffusion operator.
    operation Diffusion(numBits : Int, mark : Qubit[]) : Unit {
        // Apply Hadamard gates to all qubits.
        within {
            ApplyToEachA(H, mark);
        } apply {
            // Apply the phase flip.
            within {
                ApplyToEachA(X, mark);
            } apply {
                Z(mark[0]);
            }
            within {
                ApplyToEachA(X, mark);
            } apply {
                ApplyToEachA(H, mark);
            }
        }
    }
    operation Collision(F : ((Int, Int) -> Int), KI : Int) : (Int, Int) {
        // Define the size of the search space X.
        let X_ = 1 <<< KI;
        Message($"Search Space: ({X_})");
        // Step 1: Pick an arbitrary subset K of X of cardinality k.
        // We can generate a random subset by generating k random bits.
        let KB = GeneraterandomInt(X_,KI);
        // Construct a table L of size k where each item in L holds a distinct pair (x, F(x)) with x ∈ K.
        mutable Fx = ConstantArray(KI, 0);
        mutable x_array = ConstantArray(KI,0);
        for i in 0 .. KI - 1 {
            let index = GetRandomIndex(KI-1);
            let x = KB[index];
            let fx = F(x,X_);
            set Fx w/= i <- fx;
            set x_array w/= i <- x;
        }
        
        mutable L = Zipped(x_array,Fx);
        let sorted_L = Sorted(CompareSecond,L);
        Message($"Table L: ({L})");
        
        // // Step 2: Sort L according to the second entry in each item of L.
        Message($"Sorted Table L: ({sorted_L})");
        mutable Table = TupleArrayAsNestedArray(sorted_L);
        Message($"Table in Array Form: {Table}");
        
        // Step 3: Check if L contains a collision.
        for i in 0 .. (KI - 2) {
            if (Table[i][1] == Table[i+1][1]){
                // Step 6: Output the collision {x0, x1}.
                return (i, i+1);
            }
        }
        
        // Step 4: Compute x1 = Grover(H, 1).
        let x1 = GroverSearch(F,X_,Table);
        // // Step 5: Find (x0, F(x1)) ∈ L.
        for i in 0 .. (KI - 2) {
            if (Table[i][0] == x1){
                // Step 6: Output the collision {x0, x1}.
                return (i, -1);
            }
        }
        return (KI,1);                
    }
    
    function Fun(x : Int, N : Int) : Int {
        let xSquared = PowI(x, 2);
        let remainder = ModI(xSquared, N);
        return remainder;
    }
    @EntryPoint()
    operation FindCollision() : Unit{
        let KI = 10;
        let (i, j) = Collision(Fun, KI);
        if i == -1{
            Message($"Collision found at Value: ({i})");    
        }else{
            Message($"Collision found at index: ({i}, {j})");
        }
    }

}
