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
	case 3: // STATE 1 - model.pml:91 - [flag[0] = 0] (0:0:1 - 1)
		IfNotBlocked
		reached[1][1] = 1;
		(trpt+1)->bup.oval = ((int)now.flag[0]);
		now.flag[0] = 0;
#ifdef VAR_RANGES
		logval("flag[0]", ((int)now.flag[0]));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 4: // STATE 2 - model.pml:92 - [flag[1] = 0] (0:0:1 - 1)
		IfNotBlocked
		reached[1][2] = 1;
		(trpt+1)->bup.oval = ((int)now.flag[1]);
		now.flag[1] = 0;
#ifdef VAR_RANGES
		logval("flag[1]", ((int)now.flag[1]));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 5: // STATE 3 - model.pml:93 - [turn = 0] (0:0:1 - 1)
		IfNotBlocked
		reached[1][3] = 1;
		(trpt+1)->bup.oval = ((int)now.turn);
		now.turn = 0;
#ifdef VAR_RANGES
		logval("turn", ((int)now.turn));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 6: // STATE 4 - model.pml:95 - [request[0] = 0] (0:0:1 - 1)
		IfNotBlocked
		reached[1][4] = 1;
		(trpt+1)->bup.oval = ((int)request[0]);
		request[0] = 0;
#ifdef VAR_RANGES
		logval("request[0]", ((int)request[0]));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 7: // STATE 5 - model.pml:96 - [request[1] = 0] (0:0:1 - 1)
		IfNotBlocked
		reached[1][5] = 1;
		(trpt+1)->bup.oval = ((int)request[1]);
		request[1] = 0;
#ifdef VAR_RANGES
		logval("request[1]", ((int)request[1]));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 8: // STATE 6 - model.pml:97 - [in_cs[0] = 0] (0:0:1 - 1)
		IfNotBlocked
		reached[1][6] = 1;
		(trpt+1)->bup.oval = ((int)in_cs[0]);
		in_cs[0] = 0;
#ifdef VAR_RANGES
		logval("in_cs[0]", ((int)in_cs[0]));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 9: // STATE 7 - model.pml:98 - [in_cs[1] = 0] (0:0:1 - 1)
		IfNotBlocked
		reached[1][7] = 1;
		(trpt+1)->bup.oval = ((int)in_cs[1]);
		in_cs[1] = 0;
#ifdef VAR_RANGES
		logval("in_cs[1]", ((int)in_cs[1]));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 10: // STATE 8 - model.pml:101 - [(run P(0))] (0:0:0 - 1)
		IfNotBlocked
		reached[1][8] = 1;
		if (!(addproc(II, 1, 0, 0)))
			continue;
		_m = 3; goto P999; /* 0 */
	case 11: // STATE 9 - model.pml:102 - [(run P(1))] (0:0:0 - 1)
		IfNotBlocked
		reached[1][9] = 1;
		if (!(addproc(II, 1, 0, 1)))
			continue;
		_m = 3; goto P999; /* 0 */
	case 12: // STATE 10 - model.pml:103 - [-end-] (0:0:0 - 1)
		IfNotBlocked
		reached[1][10] = 1;
		if (!delproc(1, II)) continue;
		_m = 3; goto P999; /* 0 */

		 /* PROC P */
	case 13: // STATE 2 - model.pml:40 - [request[id] = 1] (0:0:1 - 1)
		IfNotBlocked
		reached[0][2] = 1;
		(trpt+1)->bup.oval = ((int)request[ Index(((int)((P0 *)_this)->id), 2) ]);
		request[ Index(((P0 *)_this)->id, 2) ] = 1;
#ifdef VAR_RANGES
		logval("request[P:id]", ((int)request[ Index(((int)((P0 *)_this)->id), 2) ]));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 14: // STATE 3 - model.pml:43 - [flag[id] = 1] (0:0:1 - 1)
		IfNotBlocked
		reached[0][3] = 1;
		(trpt+1)->bup.oval = ((int)now.flag[ Index(((int)((P0 *)_this)->id), 2) ]);
		now.flag[ Index(((P0 *)_this)->id, 2) ] = 1;
#ifdef VAR_RANGES
		logval("flag[P:id]", ((int)now.flag[ Index(((int)((P0 *)_this)->id), 2) ]));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 15: // STATE 4 - model.pml:47 - [turn = (1-id)] (0:0:1 - 1)
		IfNotBlocked
		reached[0][4] = 1;
		(trpt+1)->bup.oval = ((int)now.turn);
		now.turn = (1-((int)((P0 *)_this)->id));
#ifdef VAR_RANGES
		logval("turn", ((int)now.turn));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 16: // STATE 5 - model.pml:55 - [((flag[(1-id)]&&(turn==(1-id))))] (0:0:0 - 1)
		IfNotBlocked
		reached[0][5] = 1;
		if (!((((int)now.flag[ Index((1-((int)((P0 *)_this)->id)), 2) ])&&(((int)now.turn)==(1-((int)((P0 *)_this)->id))))))
			continue;
		_m = 3; goto P999; /* 0 */
	case 17: // STATE 12 - model.pml:67 - [in_cs[id] = 1] (0:0:1 - 3)
		IfNotBlocked
		reached[0][12] = 1;
		(trpt+1)->bup.oval = ((int)in_cs[ Index(((int)((P0 *)_this)->id), 2) ]);
		in_cs[ Index(((P0 *)_this)->id, 2) ] = 1;
#ifdef VAR_RANGES
		logval("in_cs[P:id]", ((int)in_cs[ Index(((int)((P0 *)_this)->id), 2) ]));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 18: // STATE 13 - model.pml:69 - [cs_count = (cs_count+1)] (0:0:1 - 1)
		IfNotBlocked
		reached[0][13] = 1;
		(trpt+1)->bup.oval = ((int)cs_count);
		cs_count = (((int)cs_count)+1);
#ifdef VAR_RANGES
		logval("cs_count", ((int)cs_count));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 19: // STATE 15 - model.pml:77 - [cs_count = (cs_count-1)] (0:0:1 - 1)
		IfNotBlocked
		reached[0][15] = 1;
		(trpt+1)->bup.oval = ((int)cs_count);
		cs_count = (((int)cs_count)-1);
#ifdef VAR_RANGES
		logval("cs_count", ((int)cs_count));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 20: // STATE 16 - model.pml:79 - [in_cs[id] = 0] (0:0:1 - 1)
		IfNotBlocked
		reached[0][16] = 1;
		(trpt+1)->bup.oval = ((int)in_cs[ Index(((int)((P0 *)_this)->id), 2) ]);
		in_cs[ Index(((P0 *)_this)->id, 2) ] = 0;
#ifdef VAR_RANGES
		logval("in_cs[P:id]", ((int)in_cs[ Index(((int)((P0 *)_this)->id), 2) ]));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 21: // STATE 17 - model.pml:82 - [flag[id] = 0] (0:0:1 - 1)
		IfNotBlocked
		reached[0][17] = 1;
		(trpt+1)->bup.oval = ((int)now.flag[ Index(((int)((P0 *)_this)->id), 2) ]);
		now.flag[ Index(((P0 *)_this)->id, 2) ] = 0;
#ifdef VAR_RANGES
		logval("flag[P:id]", ((int)now.flag[ Index(((int)((P0 *)_this)->id), 2) ]));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 22: // STATE 18 - model.pml:84 - [request[id] = 0] (0:0:1 - 1)
		IfNotBlocked
		reached[0][18] = 1;
		(trpt+1)->bup.oval = ((int)request[ Index(((int)((P0 *)_this)->id), 2) ]);
		request[ Index(((P0 *)_this)->id, 2) ] = 0;
#ifdef VAR_RANGES
		logval("request[P:id]", ((int)request[ Index(((int)((P0 *)_this)->id), 2) ]));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 23: // STATE 22 - model.pml:86 - [-end-] (0:0:0 - 1)
		IfNotBlocked
		reached[0][22] = 1;
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

