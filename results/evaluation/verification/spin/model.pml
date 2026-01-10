// Promela model for calculating maximum total chocolates from tiles

// Define system parameters using #define for easy modification and model checking
// N: Total number of tiles
// A: Divisor for painting Red
// B: Divisor for painting Blue
// P: Chocolates for Red
// Q: Chocolates for Blue
#define N 10 // Example: 10 tiles
#define A 2  // Example: Divisible by 2 for Red
#define B 3  // Example: Divisible by 3 for Blue
#define P 5  // Example: 5 chocolates for Red
#define Q 7  // Example: 7 chocolates for Blue

// Global variable to store the accumulated total chocolates
int total_chocolates = 0;

// Global variable to track the ID of the tile currently being processed.
// This is crucial for formulating LTL properties that refer to specific tile conditions.
int current_tile_id = 0;

// Global variable to store the chocolates awarded for the current tile.
// This allows LTL properties to verify the outcome of the decision logic for each tile.
int current_tile_chocolates = 0;

// Flag to indicate that the entire calculation process has completed.
bool calculation_done = false;

// The main process responsible for iterating through tiles and calculating chocolates.
proctype Calculator() {
    int i; // Loop counter for tile ID

    // Iterate through each tile from 1 to N
    for (i = 1; i <= N; i++) {
        current_tile_id = i; // Update the global tile ID for LTL verification
        current_tile_chocolates = 0; // Reset chocolates for the new tile

        // Determine divisibility conditions
        bool div_a = (i % A == 0);
        bool div_b = (i % B == 0);

        // Use an atomic block to ensure that the decision logic and the update
        // to total_chocolates for a single tile are treated as an indivisible step.
        // While not strictly necessary for a purely sequential process, it demonstrates
        // proper synchronization primitive usage and ensures consistency if this
        // were part of a larger concurrent system or if the decision itself was non-deterministic.
        atomic {
            if (div_a && div_b) {
                // Rule: If divisible by both A and B, choose the color giving more chocolates
                if (P > Q) {
                    current_tile_chocolates = P;
                } else { // Q >= P (includes case P == Q, where Q is chosen)
                    current_tile_chocolates = Q;
                }
            } else if (div_a) {
                // Rule: Divisible only by A, paint Red
                current_tile_chocolates = P;
            } else if (div_b) {
                // Rule: Divisible only by B, paint Blue
                current_tile_chocolates = Q;
            } else {
                // Rule: Not divisible by A or B, no chocolates
                current_tile_chocolates = 0;
            }
            // Add the chocolates for the current tile to the running total
            total_chocolates += current_tile_chocolates;
        }
    }
    calculation_done = true; // Signal that the calculation is complete
}

// The initial process that starts the Calculator.
init {
    run Calculator();
}