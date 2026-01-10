	switch (t->back) {
	default: Uerror("bad return move");
	case  0: goto R999; /* nothing to undo */

		 /* PROC :init: */

	case 3: // STATE 1
		;
		;
		delproc(0, now._nr_pr-1);
		;
		goto R999;

	case 4: // STATE 2
		;
		;
		delproc(0, now._nr_pr-1);
		;
		goto R999;

	case 5: // STATE 3
		;
		p_restor(II);
		;
		;
		goto R999;

		 /* PROC P2 */

	case 6: // STATE 2
		;
		P2_request = trpt->bup.oval;
		;
		goto R999;

	case 7: // STATE 4
		;
		now.sem = trpt->bup.oval;
		;
		goto R999;

	case 8: // STATE 6
		;
		P2_request = trpt->bup.oval;
		;
		goto R999;

	case 9: // STATE 7
		;
		critical_section_count = trpt->bup.oval;
		;
		goto R999;

	case 10: // STATE 8
		;
		P2_in_CS = trpt->bup.oval;
		;
		goto R999;

	case 11: // STATE 10
		;
		P2_in_CS = trpt->bup.oval;
		;
		goto R999;

	case 12: // STATE 11
		;
		critical_section_count = trpt->bup.oval;
		;
		goto R999;

	case 13: // STATE 12
		;
		now.sem = trpt->bup.oval;
		;
		goto R999;

	case 14: // STATE 17
		;
		p_restor(II);
		;
		;
		goto R999;

		 /* PROC P1 */

	case 15: // STATE 2
		;
		P1_request = trpt->bup.oval;
		;
		goto R999;

	case 16: // STATE 4
		;
		now.sem = trpt->bup.oval;
		;
		goto R999;

	case 17: // STATE 6
		;
		P1_request = trpt->bup.oval;
		;
		goto R999;

	case 18: // STATE 7
		;
		critical_section_count = trpt->bup.oval;
		;
		goto R999;

	case 19: // STATE 8
		;
		P1_in_CS = trpt->bup.oval;
		;
		goto R999;

	case 20: // STATE 10
		;
		P1_in_CS = trpt->bup.oval;
		;
		goto R999;

	case 21: // STATE 11
		;
		critical_section_count = trpt->bup.oval;
		;
		goto R999;

	case 22: // STATE 12
		;
		now.sem = trpt->bup.oval;
		;
		goto R999;

	case 23: // STATE 17
		;
		p_restor(II);
		;
		;
		goto R999;
	}

