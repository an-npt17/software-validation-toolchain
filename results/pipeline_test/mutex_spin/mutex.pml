/* Mutex with two processes - Potential Deadlock */
byte lock = 0;
byte critical = 0;

active proctype Process0() {
    do
    :: atomic {
        lock == 0;
        lock = 1;
        critical++;
        assert(critical == 1); /* Mutual exclusion */
        critical--;
        lock = 0;
    }
    od
}

active proctype Process1() {
    do
    :: atomic {
        lock == 0;
        lock = 1;
        critical++;
        assert(critical == 1); /* Mutual exclusion */
        critical--;
        lock = 0;
    }
    od
}

/* LTL Properties */
ltl mutex { [] (critical <= 1) }
ltl progress { []<> (critical == 1) }
