	switch (t->back) {
	default: Uerror("bad return move");
	case  0: goto R999; /* nothing to undo */

		 /* PROC :init: */
;
		;
		
	case 4: // STATE 3
		;
		now.current_sum = trpt->bup.ovals[1];
		now.temp_num = trpt->bup.ovals[0];
		;
		ungrab_ints(trpt->bup.ovals, 2);
		goto R999;

	case 5: // STATE 6
		;
		now.temp_num = trpt->bup.ovals[1];
		now.current_sum = trpt->bup.ovals[0];
		;
		ungrab_ints(trpt->bup.ovals, 2);
		goto R999;

	case 6: // STATE 13
		;
		now.max_sum_digits = trpt->bup.oval;
		;
		goto R999;

	case 7: // STATE 14
		;
		now.result_number = trpt->bup.oval;
		;
		goto R999;

	case 8: // STATE 15
		;
		now.prev_max_sum_digits = trpt->bup.oval;
		;
		goto R999;
;
		;
		;
		;
		
	case 11: // STATE 18
		;
		now.current_num = trpt->bup.oval;
		;
		goto R999;

	case 12: // STATE 20
		;
		now.current_sum = trpt->bup.ovals[1];
		now.temp_num = trpt->bup.ovals[0];
		;
		ungrab_ints(trpt->bup.ovals, 2);
		goto R999;

	case 13: // STATE 23
		;
		now.temp_num = trpt->bup.ovals[1];
		now.current_sum = trpt->bup.ovals[0];
		;
		ungrab_ints(trpt->bup.ovals, 2);
		goto R999;

	case 14: // STATE 30
		;
		now.prev_max_sum_digits = trpt->bup.oval;
		;
		goto R999;

	case 15: // STATE 33
		;
		now.result_number = trpt->bup.ovals[1];
		now.max_sum_digits = trpt->bup.ovals[0];
		;
		ungrab_ints(trpt->bup.ovals, 2);
		goto R999;
;
		
	case 16: // STATE 39
		goto R999;

	case 17: // STATE 35
		;
		now.result_number = trpt->bup.oval;
		;
		goto R999;
;
		
	case 18: // STATE 37
		goto R999;
;
		;
		
	case 20: // STATE 42
		;
		now.max_sum_digits_violation = trpt->bup.oval;
		;
		goto R999;
;
		;
		;
		;
		;
		;
		;
		;
		;
		;
		;
		;
		
	case 27: // STATE 58
		;
		p_restor(II);
		;
		;
		goto R999;
	}

