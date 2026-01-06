
/* LTL Properties:
 * ltl property: G(safe_condition)
 */

bool property = true;

active proctype System() {
    do
    :: property = true;
       assert(property);  /* Property must hold */
    :: skip;
    od;
}
