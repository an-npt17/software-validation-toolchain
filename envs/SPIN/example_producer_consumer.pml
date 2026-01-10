/*
 * Producer-Consumer Problem with Bounded Buffer
 * Classic synchronization example for SPIN
 */

#define BUFFER_SIZE 5
#define NUM_ITEMS 3

mtype = { msg };
chan buffer = [BUFFER_SIZE] of { mtype };

byte produced = 0;
byte consumed = 0;

/* LTL Properties */

/* Safety: Never overflow the buffer */
ltl buffer_safe { [](len(buffer) <= BUFFER_SIZE) }

/* Safety: Never consume more than produced */
ltl consume_safety { [](consumed <= produced) }

/* Liveness: All produced items are eventually consumed */
ltl eventual_consumption { <>(consumed == NUM_ITEMS) }

/* Progress: Producer makes progress */
ltl producer_progress { [](<>(produced > 0)) }

/* Progress: Consumer makes progress */  
ltl consumer_progress { [](<>(consumed > 0)) }

/* Producer process */
active proctype producer() {
    byte count = 0;
    
    do
    :: (count < NUM_ITEMS) ->
        /* Produce an item */
        buffer!msg;
        count++;
        produced++;
        printf("Produced item %d\n", count);
    :: (count >= NUM_ITEMS) -> break;
    od;
    
    printf("Producer finished\n");
}

/* Consumer process */
active proctype consumer() {
    byte count = 0;
    
    do
    :: (count < NUM_ITEMS) ->
        /* Consume an item */
        buffer?msg;
        count++;
        consumed++;
        printf("Consumed item %d\n", count);
    :: (count >= NUM_ITEMS) -> break;
    od;
    
    printf("Consumer finished\n");
}

/* Monitor to check invariants */
active proctype monitor() {
    do
    :: assert(consumed <= produced);
    :: assert(len(buffer) <= BUFFER_SIZE);
    :: (consumed == NUM_ITEMS && produced == NUM_ITEMS) -> break;
    od;
}

/*
 * Verification commands:
 *
 * Basic verification:
 *   spin -a producer_consumer.pml
 *   gcc -o pan pan.c
 *   ./pan -a
 *
 * Check for deadlocks:
 *   ./pan -l
 *
 * Generate simulation trail:
 *   spin -t producer_consumer.pml
 *
 * Verify specific property:
 *   ./pan -a -N buffer_safe
 */
