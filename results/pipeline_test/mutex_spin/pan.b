	switch (t->back) {
	default: Uerror("bad return move");
	case  0: goto R999; /* nothing to undo */

		 /* CLAIM progress */
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

		 /* CLAIM mutex */
;
		
	case 6: // STATE 1
		goto R999;

	case 7: // STATE 10
		;
		p_restor(II);
		;
		;
		goto R999;

		 /* PROC Process1 */

	case 8: // STATE 6
		;
		now.lock = trpt->bup.ovals[3];
		now.critical = trpt->bup.ovals[2];
		now.critical = trpt->bup.ovals[1];
		now.lock = trpt->bup.ovals[0];
		;
		ungrab_ints(trpt->bup.ovals, 4);
		goto R999;

	case 9: // STATE 11
		;
		p_restor(II);
		;
		;
		goto R999;

		 /* PROC Process0 */

	case 10: // STATE 6
		;
		now.lock = trpt->bup.ovals[3];
		now.critical = trpt->bup.ovals[2];
		now.critical = trpt->bup.ovals[1];
		now.lock = trpt->bup.ovals[0];
		;
		ungrab_ints(trpt->bup.ovals, 4);
		goto R999;

	case 11: // STATE 11
		;
		p_restor(II);
		;
		;
		goto R999;
	}

