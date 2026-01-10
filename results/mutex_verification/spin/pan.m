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
	case 3: // STATE 1 - model.pml:90 - [(run P1())] (0:0:0 - 1)
		IfNotBlocked
		reached[2][1] = 1;
		if (!(addproc(II, 1, 0)))
			continue;
		_m = 3; goto P999; /* 0 */
	case 4: // STATE 2 - model.pml:91 - [(run P2())] (0:0:0 - 1)
		IfNotBlocked
		reached[2][2] = 1;
		if (!(addproc(II, 1, 1)))
			continue;
		_m = 3; goto P999; /* 0 */
	case 5: // STATE 3 - model.pml:92 - [-end-] (0:0:0 - 1)
		IfNotBlocked
		reached[2][3] = 1;
		if (!delproc(1, II)) continue;
		_m = 3; goto P999; /* 0 */

		 /* PROC P2 */
	case 6: // STATE 2 - model.pml:64 - [P2_request = 1] (0:0:1 - 1)
		IfNotBlocked
		reached[1][2] = 1;
		(trpt+1)->bup.oval = ((int)P2_request);
		P2_request = 1;
#ifdef VAR_RANGES
		logval("P2_request", ((int)P2_request));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 7: // STATE 3 - model.pml:68 - [((sem>0))] (6:0:1 - 1)
		IfNotBlocked
		reached[1][3] = 1;
		if (!((((int)now.sem)>0)))
			continue;
		/* merge: sem = (sem-1)(0, 4, 6) */
		reached[1][4] = 1;
		(trpt+1)->bup.oval = ((int)now.sem);
		now.sem = (((int)now.sem)-1);
#ifdef VAR_RANGES
		logval("sem", ((int)now.sem));
#endif
		;
		_m = 3; goto P999; /* 1 */
	case 8: // STATE 6 - model.pml:71 - [P2_request = 0] (0:0:1 - 1)
		IfNotBlocked
		reached[1][6] = 1;
		(trpt+1)->bup.oval = ((int)P2_request);
		P2_request = 0;
#ifdef VAR_RANGES
		logval("P2_request", ((int)P2_request));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 9: // STATE 7 - model.pml:74 - [critical_section_count = (critical_section_count+1)] (0:0:1 - 1)
		IfNotBlocked
		reached[1][7] = 1;
		(trpt+1)->bup.oval = ((int)critical_section_count);
		critical_section_count = (((int)critical_section_count)+1);
#ifdef VAR_RANGES
		logval("critical_section_count", ((int)critical_section_count));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 10: // STATE 8 - model.pml:75 - [P2_in_CS = 1] (0:0:1 - 1)
		IfNotBlocked
		reached[1][8] = 1;
		(trpt+1)->bup.oval = ((int)P2_in_CS);
		P2_in_CS = 1;
#ifdef VAR_RANGES
		logval("P2_in_CS", ((int)P2_in_CS));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 11: // STATE 10 - model.pml:78 - [P2_in_CS = 0] (0:0:1 - 1)
		IfNotBlocked
		reached[1][10] = 1;
		(trpt+1)->bup.oval = ((int)P2_in_CS);
		P2_in_CS = 0;
#ifdef VAR_RANGES
		logval("P2_in_CS", ((int)P2_in_CS));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 12: // STATE 11 - model.pml:79 - [critical_section_count = (critical_section_count-1)] (0:0:1 - 1)
		IfNotBlocked
		reached[1][11] = 1;
		(trpt+1)->bup.oval = ((int)critical_section_count);
		critical_section_count = (((int)critical_section_count)-1);
#ifdef VAR_RANGES
		logval("critical_section_count", ((int)critical_section_count));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 13: // STATE 12 - model.pml:83 - [sem = (sem+1)] (0:0:1 - 1)
		IfNotBlocked
		reached[1][12] = 1;
		(trpt+1)->bup.oval = ((int)now.sem);
		now.sem = (((int)now.sem)+1);
#ifdef VAR_RANGES
		logval("sem", ((int)now.sem));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 14: // STATE 17 - model.pml:86 - [-end-] (0:0:0 - 1)
		IfNotBlocked
		reached[1][17] = 1;
		if (!delproc(1, II)) continue;
		_m = 3; goto P999; /* 0 */

		 /* PROC P1 */
	case 15: // STATE 2 - model.pml:27 - [P1_request = 1] (0:0:1 - 1)
		IfNotBlocked
		reached[0][2] = 1;
		(trpt+1)->bup.oval = ((int)P1_request);
		P1_request = 1;
#ifdef VAR_RANGES
		logval("P1_request", ((int)P1_request));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 16: // STATE 3 - model.pml:35 - [((sem>0))] (6:0:1 - 1)
		IfNotBlocked
		reached[0][3] = 1;
		if (!((((int)now.sem)>0)))
			continue;
		/* merge: sem = (sem-1)(0, 4, 6) */
		reached[0][4] = 1;
		(trpt+1)->bup.oval = ((int)now.sem);
		now.sem = (((int)now.sem)-1);
#ifdef VAR_RANGES
		logval("sem", ((int)now.sem));
#endif
		;
		_m = 3; goto P999; /* 1 */
	case 17: // STATE 6 - model.pml:38 - [P1_request = 0] (0:0:1 - 1)
		IfNotBlocked
		reached[0][6] = 1;
		(trpt+1)->bup.oval = ((int)P1_request);
		P1_request = 0;
#ifdef VAR_RANGES
		logval("P1_request", ((int)P1_request));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 18: // STATE 7 - model.pml:41 - [critical_section_count = (critical_section_count+1)] (0:0:1 - 1)
		IfNotBlocked
		reached[0][7] = 1;
		(trpt+1)->bup.oval = ((int)critical_section_count);
		critical_section_count = (((int)critical_section_count)+1);
#ifdef VAR_RANGES
		logval("critical_section_count", ((int)critical_section_count));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 19: // STATE 8 - model.pml:42 - [P1_in_CS = 1] (0:0:1 - 1)
		IfNotBlocked
		reached[0][8] = 1;
		(trpt+1)->bup.oval = ((int)P1_in_CS);
		P1_in_CS = 1;
#ifdef VAR_RANGES
		logval("P1_in_CS", ((int)P1_in_CS));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 20: // STATE 10 - model.pml:45 - [P1_in_CS = 0] (0:0:1 - 1)
		IfNotBlocked
		reached[0][10] = 1;
		(trpt+1)->bup.oval = ((int)P1_in_CS);
		P1_in_CS = 0;
#ifdef VAR_RANGES
		logval("P1_in_CS", ((int)P1_in_CS));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 21: // STATE 11 - model.pml:46 - [critical_section_count = (critical_section_count-1)] (0:0:1 - 1)
		IfNotBlocked
		reached[0][11] = 1;
		(trpt+1)->bup.oval = ((int)critical_section_count);
		critical_section_count = (((int)critical_section_count)-1);
#ifdef VAR_RANGES
		logval("critical_section_count", ((int)critical_section_count));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 22: // STATE 12 - model.pml:52 - [sem = (sem+1)] (0:0:1 - 1)
		IfNotBlocked
		reached[0][12] = 1;
		(trpt+1)->bup.oval = ((int)now.sem);
		now.sem = (((int)now.sem)+1);
#ifdef VAR_RANGES
		logval("sem", ((int)now.sem));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 23: // STATE 17 - model.pml:55 - [-end-] (0:0:0 - 1)
		IfNotBlocked
		reached[0][17] = 1;
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

