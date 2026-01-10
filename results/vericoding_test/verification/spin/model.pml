#define X 20 // The maximum number to check. Keep this value small (e.g., <= 20-30)
             // for practical state space exploration with SPIN.
             // Larger values of X will lead to state space explosion.

// Global variables to store the state of the computation
int max_sum_digits = 0;    // Stores the maximum sum of digits found so far
int result_number = 0;     // Stores the number corresponding to max_sum_digits (the largest one if ties)
int current_num = 1;       // Loop counter, representing the number currently being processed

// Helper variables for calculating the sum of digits for a number
int temp_num;              // Temporary variable for sum_digits calculation
int current_sum;           // Stores the sum of digits for the current_num

// Variables for LTL property verification:
// prev_max_sum_digits is used to check if max_sum_digits ever decreases (monotonicity)
int prev_max_sum_digits;
bool max_sum_digits_violation = false; // Set to true if monotonicity is violated

// This is a purely sequential algorithm, so a single 'init' process is sufficient.
// No concurrent processes, channels, or semaphores are needed as there's no concurrency
// to model or synchronize. 'atomic' blocks are used to group related operations
// into single, indivisible steps for clarity and state space reduction.
init {
    printf("Starting calculation for X = %d\n", X);

    // --- Step 1: Initialize with the first number (current_num = 1) ---
    // Calculate sum of digits for current_num (which is 1 initially)
    atomic {
        temp_num = current_num;
        current_sum = 0;
        // The loop below correctly handles positive integers.
        // A special case for temp_num == 0 is not strictly needed here as current_num starts at 1.
        do
        :: (temp_num > 0) ->
            current_sum = current_sum + (temp_num % 10); // Add the last digit
            temp_num = temp_num / 10;                     // Remove the last digit
        :: else -> break; // temp_num is 0, sum calculation complete
        od;
    }

    // Initialize max_sum_digits and result_number with the values from the first number
    max_sum_digits = current_sum;
    result_number = current_num;
    prev_max_sum_digits = max_sum_digits; // Initialize for monotonicity check

    printf("Initial: num=%d, sum=%d, max_sum=%d, result_num=%d\n", current_num, current_sum, max_sum_digits, result_number);

    // --- Step 2: Loop through numbers from 2 to X ---
    do
    :: (current_num < X) -> // Loop condition: continue as long as current_num is less than X
        current_num = current_num + 1; // Move to the next number

        // Calculate sum of digits for the new current_num
        atomic {
            temp_num = current_num;
            current_sum = 0;
            do
            :: (temp_num > 0) ->
                current_sum = current_sum + (temp_num % 10);
                temp_num = temp_num / 10;
            :: else -> break;
            od;
        }

        // Store the current max_sum_digits before potential update for monotonicity check
        prev_max_sum_digits = max_sum_digits;

        // Update max_sum_digits and result_number based on the problem rules
        atomic {
            if
            :: (current_sum > max_sum_digits) ->
                // Found a new maximum sum of digits
                max_sum_digits = current_sum;
                result_number = current_num;
            :: (current_sum == max_sum_digits) ->
                // Found a number with the same maximum sum of digits.
                // Since we iterate in increasing order (current_num is always increasing),
                // this current_num is guaranteed to be larger than any previously stored
                // result_number that had the same max_sum_digits.
                // So, we update result_number to keep the largest one.
                result_number = current_num;
            :: else -> skip; // current_sum < max_sum_digits, no update needed
            fi;
        }

        // Check for monotonicity violation: max_sum_digits should never decrease
        if
        :: (max_sum_digits < prev_max_sum_digits) ->
            max_sum_digits_violation = true;
            printf("ERROR: max_sum_digits decreased! prev=%d, current=%d\n", prev_max_sum_digits, max_sum_digits);
        :: else -> skip; // No violation
        fi;

        printf("Processing: num=%d, sum=%d, max_sum=%d, result_num=%d\n", current_num, current_sum, max_sum_digits, result_number);

    :: else -> break; // current_num has reached X, loop ends
    od;

    printf("Final result for X = %d: Number = %d, Max Sum of Digits = %d\n", X, result_number, max_sum_digits);

    // Final assertions to verify the correctness of the result for X=20
    // These assertions will cause SPIN to report an error if they are false.
    assert(result_number == 19);
    assert(max_sum_digits == 10);
    assert(!max_sum_digits_violation); // Ensure the max_sum_digits never decreased
}