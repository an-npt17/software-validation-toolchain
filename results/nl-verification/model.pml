/*
 * Promela Model Generated from Natural Language
 * Requirement: File must be opened before reading and closed after operations
 */


// Generic state machine
mtype = {{ IDLE, PROCESSING, DONE }};
mtype state = IDLE;

active proctype System() {{
    do
    :: state == IDLE ->
       state = PROCESSING;
    :: state == PROCESSING ->
       state = DONE;
    :: state == DONE ->
       break
    od
}}

// LTL Properties:
// LTL_0: G(property)
// LTL_1: G(A -> F(B))
