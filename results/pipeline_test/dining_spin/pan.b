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
;
		;
		
	case 7: // STATE 2
		;
		;
		delproc(0, now._nr_pr-1);
		;
		goto R999;

	case 8: // STATE 3
		;
		((P1 *)_this)->i = trpt->bup.oval;
		;
		goto R999;

	case 9: // STATE 4
		;
	/* 0 */	((P1 *)_this)->i = trpt->bup.oval;
		;
		;
		goto R999;

	case 10: // STATE 9
		;
		p_restor(II);
		;
		;
		goto R999;

		 /* PROC Philosopher */
;
		;
		
	case 12: // STATE 4
		;
		now.fork[ Index(((((P0 *)_this)->i+1)%3), 3) ] = trpt->bup.ovals[1];
		now.fork[ Index(((P0 *)_this)->i, 3) ] = trpt->bup.ovals[0];
		;
		ungrab_ints(trpt->bup.ovals, 2);
		goto R999;

	case 13: // STATE 7
		;
		now.eating[ Index(((P0 *)_this)->i, 3) ] = trpt->bup.oval;
		;
		goto R999;
;
		;
		
	case 15: // STATE 9
		;
		now.eating[ Index(((P0 *)_this)->i, 3) ] = trpt->bup.oval;
		;
		goto R999;

	case 16: // STATE 10
		;
		now.fork[ Index(((P0 *)_this)->i, 3) ] = trpt->bup.oval;
		;
		goto R999;

	case 17: // STATE 11
		;
		now.fork[ Index(((((P0 *)_this)->i+1)%3), 3) ] = trpt->bup.oval;
		;
		goto R999;

	case 18: // STATE 16
		;
		p_restor(II);
		;
		;
		goto R999;
	}

