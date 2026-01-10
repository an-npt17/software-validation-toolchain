#define rand	pan_rand
#define pthread_equal(a,b)	((a)==(b))
#if defined(HAS_CODE) && defined(VERBOSE)
	#ifdef BFS_PAR
		bfs_printf("Pr: %d Tr: %d\n", II, t->forw);
	#else
		cpu_printf("Pr: %d Tr: %d\n", II, t->forw);
	#endif
#endif
	switch (t->forw) {
	default: Uerror("bad forward move");
	case 0:	/* if without executable clauses */
		continue;
	case 1: /* generic 'goto' or 'skip' */
		IfNotBlocked
		_m = 3; goto P999;
	case 2: /* generic 'else' */
		IfNotBlocked
		if (trpt->o_pm&1) continue;
		_m = 3; goto P999;

		 /* PROC :init: */
	case 3: // STATE 1 - model.pml:24 - [printf('Starting calculation for X = %d\\n',20)] (0:0:0 - 1)
		IfNotBlocked
		reached[0][1] = 1;
		Printf("Starting calculation for X = %d\n", 20);
		_m = 3; goto P999; /* 0 */
	case 4: // STATE 2 - model.pml:29 - [temp_num = current_num] (0:9:2 - 1)
		IfNotBlocked
		reached[0][2] = 1;
		(trpt+1)->bup.ovals = grab_ints(2);
		(trpt+1)->bup.ovals[0] = now.temp_num;
		now.temp_num = now.current_num;
#ifdef VAR_RANGES
		logval("temp_num", now.temp_num);
#endif
		;
		/* merge: current_sum = 0(9, 3, 9) */
		reached[0][3] = 1;
		(trpt+1)->bup.ovals[1] = now.current_sum;
		now.current_sum = 0;
#ifdef VAR_RANGES
		logval("current_sum", now.current_sum);
#endif
		;
		/* merge: .(goto)(0, 10, 9) */
		reached[0][10] = 1;
		;
		_m = 3; goto P999; /* 2 */
	case 5: // STATE 4 - model.pml:34 - [((temp_num>0))] (9:0:2 - 1)
		IfNotBlocked
		reached[0][4] = 1;
		if (!((now.temp_num>0)))
			continue;
		/* merge: current_sum = (current_sum+(temp_num%10))(9, 5, 9) */
		reached[0][5] = 1;
		(trpt+1)->bup.ovals = grab_ints(2);
		(trpt+1)->bup.ovals[0] = now.current_sum;
		now.current_sum = (now.current_sum+(now.temp_num%10));
#ifdef VAR_RANGES
		logval("current_sum", now.current_sum);
#endif
		;
		/* merge: temp_num = (temp_num/10)(9, 6, 9) */
		reached[0][6] = 1;
		(trpt+1)->bup.ovals[1] = now.temp_num;
		now.temp_num = (now.temp_num/10);
#ifdef VAR_RANGES
		logval("temp_num", now.temp_num);
#endif
		;
		/* merge: .(goto)(0, 10, 9) */
		reached[0][10] = 1;
		;
		_m = 3; goto P999; /* 3 */
	case 6: // STATE 13 - model.pml:42 - [max_sum_digits = current_sum] (0:0:1 - 1)
		IfNotBlocked
		reached[0][13] = 1;
		(trpt+1)->bup.oval = now.max_sum_digits;
		now.max_sum_digits = now.current_sum;
#ifdef VAR_RANGES
		logval("max_sum_digits", now.max_sum_digits);
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 7: // STATE 14 - model.pml:43 - [result_number = current_num] (0:0:1 - 1)
		IfNotBlocked
		reached[0][14] = 1;
		(trpt+1)->bup.oval = now.result_number;
		now.result_number = now.current_num;
#ifdef VAR_RANGES
		logval("result_number", now.result_number);
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 8: // STATE 15 - model.pml:44 - [prev_max_sum_digits = max_sum_digits] (0:0:1 - 1)
		IfNotBlocked
		reached[0][15] = 1;
		(trpt+1)->bup.oval = now.prev_max_sum_digits;
		now.prev_max_sum_digits = now.max_sum_digits;
#ifdef VAR_RANGES
		logval("prev_max_sum_digits", now.prev_max_sum_digits);
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 9: // STATE 16 - model.pml:46 - [printf('Initial: num=%d, sum=%d, max_sum=%d, result_num=%d\\n',current_num,current_sum,max_sum_digits,result_number)] (0:0:0 - 1)
		IfNotBlocked
		reached[0][16] = 1;
		Printf("Initial: num=%d, sum=%d, max_sum=%d, result_num=%d\n", now.current_num, now.current_sum, now.max_sum_digits, now.result_number);
		_m = 3; goto P999; /* 0 */
	case 10: // STATE 17 - model.pml:50 - [((current_num<20))] (0:0:0 - 1)
		IfNotBlocked
		reached[0][17] = 1;
		if (!((now.current_num<20)))
			continue;
		_m = 3; goto P999; /* 0 */
	case 11: // STATE 18 - model.pml:51 - [current_num = (current_num+1)] (0:0:1 - 1)
		IfNotBlocked
		reached[0][18] = 1;
		(trpt+1)->bup.oval = now.current_num;
		now.current_num = (now.current_num+1);
#ifdef VAR_RANGES
		logval("current_num", now.current_num);
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 12: // STATE 19 - model.pml:55 - [temp_num = current_num] (0:26:2 - 1)
		IfNotBlocked
		reached[0][19] = 1;
		(trpt+1)->bup.ovals = grab_ints(2);
		(trpt+1)->bup.ovals[0] = now.temp_num;
		now.temp_num = now.current_num;
#ifdef VAR_RANGES
		logval("temp_num", now.temp_num);
#endif
		;
		/* merge: current_sum = 0(26, 20, 26) */
		reached[0][20] = 1;
		(trpt+1)->bup.ovals[1] = now.current_sum;
		now.current_sum = 0;
#ifdef VAR_RANGES
		logval("current_sum", now.current_sum);
#endif
		;
		/* merge: .(goto)(0, 27, 26) */
		reached[0][27] = 1;
		;
		_m = 3; goto P999; /* 2 */
	case 13: // STATE 21 - model.pml:58 - [((temp_num>0))] (26:0:2 - 1)
		IfNotBlocked
		reached[0][21] = 1;
		if (!((now.temp_num>0)))
			continue;
		/* merge: current_sum = (current_sum+(temp_num%10))(26, 22, 26) */
		reached[0][22] = 1;
		(trpt+1)->bup.ovals = grab_ints(2);
		(trpt+1)->bup.ovals[0] = now.current_sum;
		now.current_sum = (now.current_sum+(now.temp_num%10));
#ifdef VAR_RANGES
		logval("current_sum", now.current_sum);
#endif
		;
		/* merge: temp_num = (temp_num/10)(26, 23, 26) */
		reached[0][23] = 1;
		(trpt+1)->bup.ovals[1] = now.temp_num;
		now.temp_num = (now.temp_num/10);
#ifdef VAR_RANGES
		logval("temp_num", now.temp_num);
#endif
		;
		/* merge: .(goto)(0, 27, 26) */
		reached[0][27] = 1;
		;
		_m = 3; goto P999; /* 3 */
	case 14: // STATE 30 - model.pml:66 - [prev_max_sum_digits = max_sum_digits] (0:0:1 - 1)
		IfNotBlocked
		reached[0][30] = 1;
		(trpt+1)->bup.oval = now.prev_max_sum_digits;
		now.prev_max_sum_digits = now.max_sum_digits;
#ifdef VAR_RANGES
		logval("prev_max_sum_digits", now.prev_max_sum_digits);
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 15: // STATE 31 - model.pml:71 - [((current_sum>max_sum_digits))] (46:0:2 - 1)
		IfNotBlocked
		reached[0][31] = 1;
		if (!((now.current_sum>now.max_sum_digits)))
			continue;
		/* merge: max_sum_digits = current_sum(46, 32, 46) */
		reached[0][32] = 1;
		(trpt+1)->bup.ovals = grab_ints(2);
		(trpt+1)->bup.ovals[0] = now.max_sum_digits;
		now.max_sum_digits = now.current_sum;
#ifdef VAR_RANGES
		logval("max_sum_digits", now.max_sum_digits);
#endif
		;
		/* merge: result_number = current_num(46, 33, 46) */
		reached[0][33] = 1;
		(trpt+1)->bup.ovals[1] = now.result_number;
		now.result_number = now.current_num;
#ifdef VAR_RANGES
		logval("result_number", now.result_number);
#endif
		;
		/* merge: .(goto)(46, 39, 46) */
		reached[0][39] = 1;
		;
		_m = 3; goto P999; /* 3 */
	case 16: // STATE 39 - model.pml:84 - [.(goto)] (0:46:0 - 3)
		IfNotBlocked
		reached[0][39] = 1;
		;
		_m = 3; goto P999; /* 0 */
	case 17: // STATE 34 - model.pml:75 - [((current_sum==max_sum_digits))] (46:0:1 - 1)
		IfNotBlocked
		reached[0][34] = 1;
		if (!((now.current_sum==now.max_sum_digits)))
			continue;
		/* merge: result_number = current_num(46, 35, 46) */
		reached[0][35] = 1;
		(trpt+1)->bup.oval = now.result_number;
		now.result_number = now.current_num;
#ifdef VAR_RANGES
		logval("result_number", now.result_number);
#endif
		;
		/* merge: .(goto)(46, 39, 46) */
		reached[0][39] = 1;
		;
		_m = 3; goto P999; /* 2 */
	case 18: // STATE 37 - model.pml:82 - [(1)] (46:0:0 - 1)
		IfNotBlocked
		reached[0][37] = 1;
		if (!(1))
			continue;
		/* merge: .(goto)(46, 39, 46) */
		reached[0][39] = 1;
		;
		_m = 3; goto P999; /* 1 */
	case 19: // STATE 41 - model.pml:88 - [((max_sum_digits<prev_max_sum_digits))] (0:0:0 - 1)
		IfNotBlocked
		reached[0][41] = 1;
		if (!((now.max_sum_digits<now.prev_max_sum_digits)))
			continue;
		_m = 3; goto P999; /* 0 */
	case 20: // STATE 42 - model.pml:89 - [max_sum_digits_violation = 1] (0:0:1 - 1)
		IfNotBlocked
		reached[0][42] = 1;
		(trpt+1)->bup.oval = ((int)now.max_sum_digits_violation);
		now.max_sum_digits_violation = 1;
#ifdef VAR_RANGES
		logval("max_sum_digits_violation", ((int)now.max_sum_digits_violation));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 21: // STATE 43 - model.pml:90 - [printf('ERROR: max_sum_digits decreased! prev=%d, current=%d\\n',prev_max_sum_digits,max_sum_digits)] (0:0:0 - 1)
		IfNotBlocked
		reached[0][43] = 1;
		Printf("ERROR: max_sum_digits decreased! prev=%d, current=%d\n", now.prev_max_sum_digits, now.max_sum_digits);
		_m = 3; goto P999; /* 0 */
	case 22: // STATE 48 - model.pml:94 - [printf('Processing: num=%d, sum=%d, max_sum=%d, result_num=%d\\n',current_num,current_sum,max_sum_digits,result_number)] (0:0:0 - 3)
		IfNotBlocked
		reached[0][48] = 1;
		Printf("Processing: num=%d, sum=%d, max_sum=%d, result_num=%d\n", now.current_num, now.current_sum, now.max_sum_digits, now.result_number);
		_m = 3; goto P999; /* 0 */
	case 23: // STATE 54 - model.pml:99 - [printf('Final result for X = %d: Number = %d, Max Sum of Digits = %d\\n',20,result_number,max_sum_digits)] (0:0:0 - 3)
		IfNotBlocked
		reached[0][54] = 1;
		Printf("Final result for X = %d: Number = %d, Max Sum of Digits = %d\n", 20, now.result_number, now.max_sum_digits);
		_m = 3; goto P999; /* 0 */
	case 24: // STATE 55 - model.pml:103 - [assert((result_number==19))] (0:0:0 - 1)
		IfNotBlocked
		reached[0][55] = 1;
		spin_assert((now.result_number==19), "(result_number==19)", II, tt, t);
		_m = 3; goto P999; /* 0 */
	case 25: // STATE 56 - model.pml:104 - [assert((max_sum_digits==10))] (0:0:0 - 1)
		IfNotBlocked
		reached[0][56] = 1;
		spin_assert((now.max_sum_digits==10), "(max_sum_digits==10)", II, tt, t);
		_m = 3; goto P999; /* 0 */
	case 26: // STATE 57 - model.pml:105 - [assert(!(max_sum_digits_violation))] (0:0:0 - 1)
		IfNotBlocked
		reached[0][57] = 1;
		spin_assert( !(((int)now.max_sum_digits_violation)), " !(max_sum_digits_violation)", II, tt, t);
		_m = 3; goto P999; /* 0 */
	case 27: // STATE 58 - model.pml:106 - [-end-] (0:0:0 - 1)
		IfNotBlocked
		reached[0][58] = 1;
		if (!delproc(1, II)) continue;
		_m = 3; goto P999; /* 0 */
	case  _T5:	/* np_ */
		if (!((!(trpt->o_pm&4) && !(trpt->tau&128))))
			continue;
		/* else fall through */
	case  _T2:	/* true */
		_m = 3; goto P999;
#undef rand
	}

