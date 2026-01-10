#include <stdio.h> // Required for printf in the main function for demonstration

/*@
// Helper function (ghost function) for specification purposes.
// It defines the expected number of chocolates for a single tile based on the problem rules.
// This function is a 'logic' function in ACSL, meaning it's only used for verification
// and is not compiled into the C program's runtime code.
logic integer get_chocolates_for_tile(integer tile_num, integer a, integer b, integer p, integer q) =
    (tile_num % a == 0 && tile_num % b == 0) ? (p >= q ? p : q) : // If divisible by both 'a' and 'b', choose the color giving more chocolates.
    (tile_num % a == 0) ? p :                                    // If divisible by 'a' only, get 'p' chocolates.
    (tile_num % b == 0) ? q :                                    // If divisible by 'b' only, get 'q' chocolates.
    0;                                                           // If not divisible by 'a' or 'b', get 0 chocolates.
*/

/*@
// Function contract for calculate_max_chocolates.

// Preconditions (requires clauses):
// These conditions must hold true before the function is called.
// - n must be at least 1, ensuring there's at least one tile to process.
requires n >= 1;
// - a and b must be positive, as they represent divisors. Division by zero or negative numbers is undefined.
requires a >= 1;
requires b >= 1;
// - p and q must be non-negative, as chocolates are typically a positive or zero quantity.
requires p >= 0;
requires q >= 0;

// Frame condition (assigns clause):
// - \nothing indicates that this function does not modify any global variables or memory outside its local scope.
//   It is a pure function in terms of side effects.
assigns \nothing;

// Postconditions (ensures clauses):
// These conditions must hold true after the function has executed successfully.
// - The returned value (\result) is precisely the sum of chocolates for each tile from 1 to n,
//   calculated according to the rules defined by the ghost function 'get_chocolates_for_tile'.
ensures \result == \sum_{k=1}^{n} get_chocolates_for_tile(k, a, b, p, q);
// - The total number of chocolates calculated must always be non-negative.
ensures \result >= 0;
*/
int calculate_max_chocolates(int n, int a, int b, int p, int q) {
    // Variable to accumulate the total chocolates.
    // Initialized to 0 as no tiles have been processed yet.
    int total_chocolates = 0;

    /*@
    // Loop invariants for the main iteration over tiles (from 1 to n).
    // These properties must be true at the beginning of each loop iteration and after each iteration.

    // 1. Loop counter bounds:
    //    'i' starts at 1 and increments up to 'n'. After the loop finishes, 'i' will be 'n + 1'.
    loop invariant 1 <= i <= n + 1;

    // 2. Accumulator correctness:
    //    'total_chocolates' correctly holds the sum of chocolates for all tiles processed so far
    //    (from 1 up to 'i-1'). This is the core correctness invariant.
    loop invariant total_chocolates == \sum_{k=1}^{i-1} get_chocolates_for_tile(k, a, b, p, q);

    // 3. Safety property:
    //    'total_chocolates' always remains non-negative throughout the loop execution.
    //    This is guaranteed by the preconditions (p, q >= 0) and the logic.
    loop invariant total_chocolates >= 0;

    // Frame condition for the loop (loop assigns clause):
    // - Specifies which variables are modified within the loop.
    //   The loop counter 'i' and the accumulator 'total_chocolates' are modified.
    loop assigns i, total_chocolates;
    */
    for (int i = 1; i <= n; ++i) {
        // Variable to store chocolates gained from the current tile 'i'.
        int current_tile_chocolates = 0;

        // Apply the painting rules:
        // Rule 1: Divisible by both 'a' and 'b'.
        if (i % a == 0 && i % b == 0) {
            // Choose the color that gives more chocolates.
            if (p >= q) {
                current_tile_chocolates = p;
            } else {
                current_tile_chocolates = q;
            }
        }
        // Rule 2: Divisible by 'a' only (and not by 'b', handled by the 'else if').
        else if (i % a == 0) {
            current_tile_chocolates = p;
        }
        // Rule 3: Divisible by 'b' only (and not by 'a', handled by the 'else if').
        else if (i % b == 0) {
            current_tile_chocolates = q;
        }
        // Rule 4: Not divisible by 'a' or 'b'.
        else {
            current_tile_chocolates = 0;
        }

        /*@
        // Assertion 1: Correctness check for the current tile's chocolates.
        // Verifies that the calculated 'current_tile_chocolates' matches the definition
        // provided by our formal ghost function 'get_chocolates_for_tile'.
        assert current_tile_chocolates == get_chocolates_for_tile(i, a, b, p, q);

        // Assertion 2: Safety property - chocolates for a single tile must be non-negative.
        // This assertion helps verify that intermediate calculations do not result in invalid states.
        // It is guaranteed by the function's preconditions (p >= 0, q >= 0).
        assert current_tile_chocolates >= 0;
        */

        // Add chocolates from the current tile to the total accumulator.
        total_chocolates += current_tile_chocolates;

        /*@
        // Assertion 3: Safety property - total chocolates must remain non-negative after each update.
        // This is guaranteed because 'current_tile_chocolates' is non-negative (as asserted above)
        // and 'total_chocolates' was non-negative before the addition (by loop invariant).
        assert total_chocolates >= 0;
        */
    }

    return total_chocolates;
}

// Main function for testing and demonstration purposes.
int main() {
    printf("--- Tile Painting Chocolate Maximization ---\n\n");

    // Test Case 1: Basic scenario (p < q for both)
    // Tiles 1-10, a=2, b=3, p=5, q=7
    // Expected: 0+5+7+5+0+7+0+5+7+5 = 41
    int n1 = 10, a1 = 2, b1 = 3, p1 = 5, q1 = 7;
    int result1 = calculate_max_chocolates(n1, a1, b1, p1, q1);
    printf("Test Case 1 (n=%d, a=%d, b=%d, p=%d, q=%d): Total chocolates = %d (Expected: 41)\n", n1, a1, b1, p1, q1, result1);

    // Test Case 2: p > q for both
    // Tiles 1-10, a=2, b=3, p=7, q=5
    // Expected: 0+7+5+7+0+7+0+7+5+7 = 45
    int n2 = 10, a2 = 2, b2 = 3, p2 = 7, q2 = 5;
    int result2 = calculate_max_chocolates(n2, a2, b2, p2, q2);
    printf("Test Case 2 (n=%d, a=%d, b=%d, p=%d, q=%d): Total chocolates = %d (Expected: 45)\n", n2, a2, b2, p2, q2, result2);

    // Test Case 3: 'a' is 1, so all tiles are divisible by 'a'.
    // Tiles 1-5, a=1, b=10, p=10, q=1
    // Expected: 10*5 = 50 (all tiles get 10 chocolates)
    int n3 = 5, a3 = 1, b3 = 10, p3 = 10, q3 = 1;
    int result3 = calculate_max_chocolates(n3, a3, b3, p3, q3);
    printf("Test Case 3 (n=%d, a=%d, b=%d, p=%d, q=%d): Total chocolates = %d (Expected: 50)\n", n3, a3, b3, p3, q3, result3);

    // Test Case 4: Edge case - n=1, both a and b are 1.
    // Tile 1, a=1, b=1, p=10, q=20
    // Expected: 20 (div by 1,1; q > p)
    int n4 = 1, a4 = 1, b4 = 1, p4 = 10, q4 = 20;
    int result4 = calculate_max_chocolates(n4, a4, b4, p4, q4);
    printf("Test Case 4 (n=%d, a=%d, b=%d, p=%d, q=%d): Total chocolates = %d (Expected: 20)\n", n4, a4, b4, p4, q4, result4);

    // Test Case 5: Zero chocolates for 'p'
    // Tiles 1-5, a=2, b=3, p=0, q=5
    // Expected: 0+0+5+0+0 = 5
    int n5 = 5, a5 = 2, b5 = 3, p5 = 0, q5 = 5;
    int result5 = calculate_max_chocolates(n5, a5, b5, p5, q5);
    printf("Test Case 5 (n=%d, a=%d, b=%d, p=%d, q=%d): Total chocolates = %d (Expected: 5)\n", n5, a5, b5, p5, q5, result5);

    printf("\n--- End of Demonstration ---\n");

    return 0;
}