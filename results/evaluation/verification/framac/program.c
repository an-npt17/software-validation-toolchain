#include <stdbool.h> // For bool type
#include <string.h>  // For strlen
#include <stdio.h>   // For printf in main function

/*@
  @  requires \true; // No specific preconditions for a single character
  @  ensures \result == \true || \result == \false;
  @  assigns \nothing; // This function does not modify any state
  @*/
/**
 * @brief Checks if a given character is one of the defined symmetric characters.
 *        Symmetric characters: A, H, I, M, O, o, T, U, V, v, W, w, X, x, Y
 * @param c The character to check.
 * @return true if the character is symmetric, false otherwise.
 */
bool is_symmetric_char(char c) {
    switch (c) {
        case 'A': case 'H': case 'I': case 'M': case 'O': case 'o':
        case 'T': case 'U': case 'V': case 'v': case 'W': case 'w':
        case 'X': case 'x': case 'Y':
            return true;
        default:
            return false;
    }
}

/*@
  @  requires \true; // No specific preconditions for two characters
  @  ensures \result == \true || \result == \false;
  @  assigns \nothing; // This function does not modify any state
  @*/
/**
 * @brief Checks if two characters form a valid s-palindrome mirror pair.
 *        This includes identical symmetric characters or specific mirror pairs (p,q), (b,d).
 * @param c1 The character from the left side of the string.
 * @param c2 The character from the right side of the string.
 * @return true if c1 is the mirror image of c2, false otherwise.
 */
bool is_mirror_of(char c1, char c2) {
    // Case 1: c1 is a symmetric character, then c2 must be identical to c1.
    if (is_symmetric_char(c1)) {
        return c1 == c2;
    }
    // Case 2: c1 is part of a mirror pair.
    switch (c1) {
        case 'p': return c2 == 'q';
        case 'q': return c2 == 'p';
        case 'b': return c2 == 'd';
        case 'd': return c2 == 'b';
        default:
            // Case 3: c1 is not an allowed character for s-palindromes.
            // Therefore, it cannot form a valid mirror pair.
            return false;
    }
}

/*@
  @  requires s != \null; // The input string pointer must not be NULL.
  @  requires \valid(s + (0 .. strlen(s))); // The string must be null-terminated and all characters up to the null terminator must be valid.
  @  ensures \result == \true || \result == \false; // The function always returns a boolean value.
  @  assigns \nothing; // This function only reads from the string 's' and does not modify any state.
  @*/
/**
 * @brief Checks if a string is an "s-palindrome".
 *        An s-palindrome is symmetric when mirrored horizontally about its center.
 *        - Symmetric letters: A, H, I, M, O, o, T, U, V, v, W, w, X, x, Y (must match themselves)
 *        - Mirror pairs: (p,q) and (b,d) (must match their pair)
 *        - All other letters cannot form valid s-palindromes.
 * @param s The string to check.
 * @return true if the string is an s-palindrome, false otherwise.
 */
bool is_s_palindrome(const char *s) {
    size_t len = strlen(s); // Get the length of the string.

    // An empty string is considered an s-palindrome.
    if (len == 0) {
        return true;
    }

    // If the string length is odd, the middle character must be a symmetric character itself.
    if (len % 2 != 0) {
        /*@ assert 0 <= len / 2 < len; */ // Assert: The middle character index is within string bounds.
        if (!is_symmetric_char(s[len / 2])) {
            return false;
        }
    }

    // Iterate from the start of the string towards the middle.
    /*@
      @  loop invariant 0 <= i <= len / 2; // Loop counter 'i' is always within valid bounds relative to half the string length.
      @  loop invariant \forall integer k; 0 <= k < i ==> is_mirror_of(s[k], s[len - 1 - k]);
      @     // For all characters already checked (from index 0 up to i-1),
      @     // the character at index k is a mirror image of the character at index (len - 1 - k).
      @  loop assigns i; // Only the loop counter 'i' is modified within the loop.
      @  loop variant len / 2 - i; // The loop terminates because 'i' increases towards 'len / 2',
      @                           // making this variant a decreasing non-negative integer.
      @*/
    for (size_t i = 0; i < len / 2; ++i) {
        /*@ assert 0 <= i < len; */ // Assert: The left character index is within string bounds.
        /*@ assert 0 <= len - 1 - i < len; */ // Assert: The right character index is within string bounds.
        // Check if the character at 'i' and its mirrored counterpart at 'len - 1 - i' form a valid s-palindrome pair.
        if (!is_mirror_of(s[i], s[len - 1 - i])) {
            return false; // If any pair is not a mirror, it's not an s-palindrome.
        }
    }

    // If all checks pass, the string is an s-palindrome.
    return true;
}

// Main function for demonstration and testing
int main() {
    // Test cases for the s-palindrome checker
    const char *test_strings[] = {
        "",             // Expected: TRUE (empty string)
        "A",            // Expected: TRUE (single symmetric char)
        "B",            // Expected: FALSE (single non-symmetric char)
        "AA",           // Expected: TRUE (two symmetric chars)
        "pq",           // Expected: TRUE (mirror pair)
        "qp",           // Expected: TRUE (mirror pair reversed)
        "bd",           // Expected: TRUE (mirror pair)
        "db",           // Expected: TRUE (mirror pair reversed)
        "pAq",          // Expected: TRUE (odd length, middle symmetric)
        "pBq",          // Expected: FALSE (odd length, middle non-symmetric)
        "AHHA",         // Expected: TRUE (longer symmetric)
        "pXq",          // Expected: TRUE (longer symmetric with mirror pair)
        "pXb",          // Expected: FALSE (invalid mirror pair)
        "pXQ",          // Expected: FALSE (invalid case sensitive mirror pair)
        "s-palindrome", // Expected: FALSE (contains invalid chars)
        "oOo",          // Expected: TRUE
        "wWw",          // Expected: TRUE
        "xXx",          // Expected: TRUE
        "YyY",          // Expected: TRUE
        "pYq",          // Expected: TRUE
        "dYd",          // Expected: TRUE
        "dYp",          // Expected: FALSE (invalid pair)
        "pYd",          // Expected: FALSE (invalid pair)
        "pYp",          // Expected: FALSE (invalid pair)
        "pYqXqYp",      // Expected: TRUE (complex valid)
        "pYqXqYd"       // Expected: FALSE (complex invalid)
    };

    int num_tests = sizeof(test_strings) / sizeof(test_strings[0]);

    printf("--- S-Palindrome Checker ---\n");
    for (int i = 0; i < num_tests; ++i) {
        printf("String \"%s\": %s\n", test_strings[i], is_s_palindrome(test_strings[i]) ? "TRUE" : "FALSE");
    }

    printf("\n--- Demonstrating Potential Violations (ACSL Precondition Failures) ---\n");
    printf("These calls are commented out to prevent runtime crashes, but Frama-C would detect them.\n");

    // Potential Violation 1: Passing a NULL pointer
    // This violates `requires s != \null;`
    // const char *null_string = NULL;
    // printf("String NULL: %s\n", is_s_palindrome(null_string) ? "TRUE" : "FALSE");
    printf("1. Calling is_s_palindrome with NULL string: Frama-C would report a precondition violation for 's != \\null'.\n");

    // Potential Violation 2: Passing a non-null-terminated string
    // This violates `requires \valid(s + (0 .. strlen(s)));` because strlen would read out of bounds.
    // char non_null_terminated_buffer[5] = {'a', 'b', 'c', 'd', 'e'}; // No null terminator
    // printf("String \"abcde\" (non-null-terminated): %s\n", is_s_palindrome(non_null_terminated_buffer) ? "TRUE" : "FALSE");
    printf("2. Calling is_s_palindrome with non-null-terminated string: Frama-C would report a precondition violation for '\\valid(s + (0 .. strlen(s)))'.\n");

    return 0;
}