	switch (t->back) {
	default: Uerror("bad return move");
	case  0: goto R999; /* nothing to undo */

		 /* CLAIM no_deadlock */
;
		;
		;
		;

	case 5: // STATE 13
		;
		p_restor(II);
		;
		;
		goto R999;

		 /* PROC :init: */

	case 6: // STATE 1
		;
		((P1 *)_this)->_2_4_i = trpt->bup.oval;
		;
		goto R999;
;
		;

	case 8: // STATE 3
		;
		;
		delproc(0, now._nr_pr-1);
		;
		goto R999;

	case 9: // STATE 4
		;
		((P1 *)_this)->_2_4_i = trpt->bup.oval;
		;
		goto R999;

	case 10: // STATE 11
		;
		p_restor(II);
		;
		;
		goto R999;

		 /* PROC Philosopher */
;
		;

	case 12: // STATE 2
		;
		now.fork[ Index(((P0 *)_this)->id, 3) ] = trpt->bup.oval;
		;
		goto R999;
;
		;

	case 14: // STATE 5
		;
		now.fork[ Index(((((P0 *)_this)->id+1)%3), 3) ] = trpt->bup.oval;
		;
		goto R999;

	case 15: // STATE 7
		;
		now.eating[ Index(((P0 *)_this)->id, 3) ] = trpt->bup.oval;
		;
		goto R999;
;
		;

	case 17: // STATE 9
		;
		now.eating[ Index(((P0 *)_this)->id, 3) ] = trpt->bup.oval;
		;
		goto R999;

	case 18: // STATE 10
		;
		now.fork[ Index(((P0 *)_this)->id, 3) ] = trpt->bup.oval;
		;
		goto R999;

	case 19: // STATE 11
		;
		now.fork[ Index(((((P0 *)_this)->id+1)%3), 3) ] = trpt->bup.oval;
		;
		goto R999;

	case 20: // STATE 16
		;
		p_restor(II);
		;
		;
		goto R999;
	}

