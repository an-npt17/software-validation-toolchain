/* Dining Philosophers - Has Deadlock */
#define N 3

byte fork[N];
byte eating[N];

inline pick_forks(i) {
    atomic {
        fork[i] == 0;
        fork[(i+1) % N] == 0;
        fork[i] = 1;
        fork[(i+1) % N] = 1;
    }
}

inline put_forks(i) {
    fork[i] = 0;
    fork[(i+1) % N] = 0;
}

proctype Philosopher(byte i) {
    do
    :: /* think */
       pick_forks(i);
       eating[i] = 1;
       assert(eating[i] == 1);
       eating[i] = 0;
       put_forks(i);
    od
}

init {
    byte i = 0;
    do
    :: i < N ->
        run Philosopher(i);
        i++;
    :: i >= N -> break;
    od
}

/* This should find deadlock */
ltl no_deadlock { []<> (eating[0] == 1 || eating[1] == 1 || eating[2] == 1) }
