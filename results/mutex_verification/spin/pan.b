	switch (t->back) {
	default: Uerror("bad return move");
	case  0: goto R999; /* nothing to undo */

		 /* PROC :init: */

	case 3: // STATE 1
		;
		now.flag[0] = trpt->bup.oval;
		;
		goto R999;

	case 4: // STATE 2
		;
		now.flag[1] = trpt->bup.oval;
		;
		goto R999;

	case 5: // STATE 3
		;
		now.turn = trpt->bup.oval;
		;
		goto R999;

	case 6: // STATE 4
		;
		request[0] = trpt->bup.oval;
		;
		goto R999;

	case 7: // STATE 5
		;
		request[1] = trpt->bup.oval;
		;
		goto R999;

	case 8: // STATE 6
		;
		in_cs[0] = trpt->bup.oval;
		;
		goto R999;

	case 9: // STATE 7
		;
		in_cs[1] = trpt->bup.oval;
		;
		goto R999;

	case 10: // STATE 8
		;
		;
		delproc(0, now._nr_pr-1);
		;
		goto R999;

	case 11: // STATE 9
		;
		;
		delproc(0, now._nr_pr-1);
		;
		goto R999;

	case 12: // STATE 10
		;
		p_restor(II);
		;
		;
		goto R999;

		 /* PROC P */

	case 13: // STATE 2
		;
		request[ Index(((P0 *)_this)->id, 2) ] = trpt->bup.oval;
		;
		goto R999;

	case 14: // STATE 3
		;
		now.flag[ Index(((P0 *)_this)->id, 2) ] = trpt->bup.oval;
		;
		goto R999;

	case 15: // STATE 4
		;
		now.turn = trpt->bup.oval;
		;
		goto R999;
;
		;
		
	case 17: // STATE 12
		;
		in_cs[ Index(((P0 *)_this)->id, 2) ] = trpt->bup.oval;
		;
		goto R999;

	case 18: // STATE 13
		;
		cs_count = trpt->bup.oval;
		;
		goto R999;

	case 19: // STATE 15
		;
		cs_count = trpt->bup.oval;
		;
		goto R999;

	case 20: // STATE 16
		;
		in_cs[ Index(((P0 *)_this)->id, 2) ] = trpt->bup.oval;
		;
		goto R999;

	case 21: // STATE 17
		;
		now.flag[ Index(((P0 *)_this)->id, 2) ] = trpt->bup.oval;
		;
		goto R999;

	case 22: // STATE 18
		;
		request[ Index(((P0 *)_this)->id, 2) ] = trpt->bup.oval;
		;
		goto R999;

	case 23: // STATE 22
		;
		p_restor(II);
		;
		;
		goto R999;
	}

