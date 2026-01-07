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

		 /* CLAIM no_deadlock */
	case 3: // STATE 1 - _spin_nvr.tmp:3 - [(!((((eating[0]==1)||(eating[1]==1))||(eating[2]==1))))] (0:0:0 - 1)
		
#if defined(VERI) && !defined(NP)
#if NCLAIMS>1
		{	static int reported1 = 0;
			if (verbose && !reported1)
			{	int nn = (int) ((Pclaim *)pptr(0))->_n;
				printf("depth %ld: Claim %s (%d), state %d (line %d)\n",
					depth, procname[spin_c_typ[nn]], nn, (int) ((Pclaim *)pptr(0))->_p, src_claim[ (int) ((Pclaim *)pptr(0))->_p ]);
				reported1 = 1;
				fflush(stdout);
		}	}
#else
		{	static int reported1 = 0;
			if (verbose && !reported1)
			{	printf("depth %d: Claim, state %d (line %d)\n",
					(int) depth, (int) ((Pclaim *)pptr(0))->_p, src_claim[ (int) ((Pclaim *)pptr(0))->_p ]);
				reported1 = 1;
				fflush(stdout);
		}	}
#endif
#endif
		reached[2][1] = 1;
		if (!( !((((((int)now.eating[0])==1)||(((int)now.eating[1])==1))||(((int)now.eating[2])==1)))))
			continue;
		_m = 3; goto P999; /* 0 */
	case 4: // STATE 8 - _spin_nvr.tmp:8 - [(!((((eating[0]==1)||(eating[1]==1))||(eating[2]==1))))] (0:0:0 - 1)
		
#if defined(VERI) && !defined(NP)
#if NCLAIMS>1
		{	static int reported8 = 0;
			if (verbose && !reported8)
			{	int nn = (int) ((Pclaim *)pptr(0))->_n;
				printf("depth %ld: Claim %s (%d), state %d (line %d)\n",
					depth, procname[spin_c_typ[nn]], nn, (int) ((Pclaim *)pptr(0))->_p, src_claim[ (int) ((Pclaim *)pptr(0))->_p ]);
				reported8 = 1;
				fflush(stdout);
		}	}
#else
		{	static int reported8 = 0;
			if (verbose && !reported8)
			{	printf("depth %d: Claim, state %d (line %d)\n",
					(int) depth, (int) ((Pclaim *)pptr(0))->_p, src_claim[ (int) ((Pclaim *)pptr(0))->_p ]);
				reported8 = 1;
				fflush(stdout);
		}	}
#endif
#endif
		reached[2][8] = 1;
		if (!( !((((((int)now.eating[0])==1)||(((int)now.eating[1])==1))||(((int)now.eating[2])==1)))))
			continue;
		_m = 3; goto P999; /* 0 */
	case 5: // STATE 13 - _spin_nvr.tmp:10 - [-end-] (0:0:0 - 1)
		
#if defined(VERI) && !defined(NP)
#if NCLAIMS>1
		{	static int reported13 = 0;
			if (verbose && !reported13)
			{	int nn = (int) ((Pclaim *)pptr(0))->_n;
				printf("depth %ld: Claim %s (%d), state %d (line %d)\n",
					depth, procname[spin_c_typ[nn]], nn, (int) ((Pclaim *)pptr(0))->_p, src_claim[ (int) ((Pclaim *)pptr(0))->_p ]);
				reported13 = 1;
				fflush(stdout);
		}	}
#else
		{	static int reported13 = 0;
			if (verbose && !reported13)
			{	printf("depth %d: Claim, state %d (line %d)\n",
					(int) depth, (int) ((Pclaim *)pptr(0))->_p, src_claim[ (int) ((Pclaim *)pptr(0))->_p ]);
				reported13 = 1;
				fflush(stdout);
		}	}
#endif
#endif
		reached[2][13] = 1;
		if (!delproc(1, II)) continue;
		_m = 3; goto P999; /* 0 */

		 /* PROC :init: */
	case 6: // STATE 1 - dining_philosophers.pml:35 - [((i<3))] (0:0:0 - 1)
		IfNotBlocked
		reached[1][1] = 1;
		if (!((((int)((P1 *)_this)->i)<3)))
			continue;
		_m = 3; goto P999; /* 0 */
	case 7: // STATE 2 - dining_philosophers.pml:36 - [(run Philosopher(i))] (0:0:0 - 1)
		IfNotBlocked
		reached[1][2] = 1;
		if (!(addproc(II, 1, 0, ((int)((P1 *)_this)->i))))
			continue;
		_m = 3; goto P999; /* 0 */
	case 8: // STATE 3 - dining_philosophers.pml:37 - [i = (i+1)] (0:0:1 - 1)
		IfNotBlocked
		reached[1][3] = 1;
		(trpt+1)->bup.oval = ((int)((P1 *)_this)->i);
		((P1 *)_this)->i = (((int)((P1 *)_this)->i)+1);
#ifdef VAR_RANGES
		logval(":init::i", ((int)((P1 *)_this)->i));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 9: // STATE 4 - dining_philosophers.pml:38 - [((i>=3))] (0:0:1 - 1)
		IfNotBlocked
		reached[1][4] = 1;
		if (!((((int)((P1 *)_this)->i)>=3)))
			continue;
		if (TstOnly) return 1; /* TT */
		/* dead 1: i */  (trpt+1)->bup.oval = ((P1 *)_this)->i;
#ifdef HAS_CODE
		if (!readtrail)
#endif
			((P1 *)_this)->i = 0;
		_m = 3; goto P999; /* 0 */
	case 10: // STATE 9 - dining_philosophers.pml:40 - [-end-] (0:0:0 - 3)
		IfNotBlocked
		reached[1][9] = 1;
		if (!delproc(1, II)) continue;
		_m = 3; goto P999; /* 0 */

		 /* PROC Philosopher */
	case 11: // STATE 1 - dining_philosophers.pml:9 - [((fork[i]==0))] (0:0:0 - 1)
		IfNotBlocked
		reached[0][1] = 1;
		if (!((((int)now.fork[ Index(((int)((P0 *)_this)->i), 3) ])==0)))
			continue;
		_m = 3; goto P999; /* 0 */
	case 12: // STATE 2 - dining_philosophers.pml:10 - [((fork[((i+1)%3)]==0))] (7:0:2 - 1)
		IfNotBlocked
		reached[0][2] = 1;
		if (!((((int)now.fork[ Index(((((int)((P0 *)_this)->i)+1)%3), 3) ])==0)))
			continue;
		/* merge: fork[i] = 1(7, 3, 7) */
		reached[0][3] = 1;
		(trpt+1)->bup.ovals = grab_ints(2);
		(trpt+1)->bup.ovals[0] = ((int)now.fork[ Index(((int)((P0 *)_this)->i), 3) ]);
		now.fork[ Index(((P0 *)_this)->i, 3) ] = 1;
#ifdef VAR_RANGES
		logval("fork[Philosopher:i]", ((int)now.fork[ Index(((int)((P0 *)_this)->i), 3) ]));
#endif
		;
		/* merge: fork[((i+1)%3)] = 1(7, 4, 7) */
		reached[0][4] = 1;
		(trpt+1)->bup.ovals[1] = ((int)now.fork[ Index(((((int)((P0 *)_this)->i)+1)%3), 3) ]);
		now.fork[ Index(((((P0 *)_this)->i+1)%3), 3) ] = 1;
#ifdef VAR_RANGES
		logval("fork[((Philosopher:i+1)%3)]", ((int)now.fork[ Index(((((int)((P0 *)_this)->i)+1)%3), 3) ]));
#endif
		;
		_m = 3; goto P999; /* 2 */
	case 13: // STATE 7 - dining_philosophers.pml:25 - [eating[i] = 1] (0:0:1 - 1)
		IfNotBlocked
		reached[0][7] = 1;
		(trpt+1)->bup.oval = ((int)now.eating[ Index(((int)((P0 *)_this)->i), 3) ]);
		now.eating[ Index(((P0 *)_this)->i, 3) ] = 1;
#ifdef VAR_RANGES
		logval("eating[Philosopher:i]", ((int)now.eating[ Index(((int)((P0 *)_this)->i), 3) ]));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 14: // STATE 8 - dining_philosophers.pml:26 - [assert((eating[i]==1))] (0:0:0 - 1)
		IfNotBlocked
		reached[0][8] = 1;
		spin_assert((((int)now.eating[ Index(((int)((P0 *)_this)->i), 3) ])==1), "(eating[i]==1)", II, tt, t);
		_m = 3; goto P999; /* 0 */
	case 15: // STATE 9 - dining_philosophers.pml:27 - [eating[i] = 0] (0:0:1 - 1)
		IfNotBlocked
		reached[0][9] = 1;
		(trpt+1)->bup.oval = ((int)now.eating[ Index(((int)((P0 *)_this)->i), 3) ]);
		now.eating[ Index(((P0 *)_this)->i, 3) ] = 0;
#ifdef VAR_RANGES
		logval("eating[Philosopher:i]", ((int)now.eating[ Index(((int)((P0 *)_this)->i), 3) ]));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 16: // STATE 10 - dining_philosophers.pml:17 - [fork[i] = 0] (0:0:1 - 1)
		IfNotBlocked
		reached[0][10] = 1;
		(trpt+1)->bup.oval = ((int)now.fork[ Index(((int)((P0 *)_this)->i), 3) ]);
		now.fork[ Index(((P0 *)_this)->i, 3) ] = 0;
#ifdef VAR_RANGES
		logval("fork[Philosopher:i]", ((int)now.fork[ Index(((int)((P0 *)_this)->i), 3) ]));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 17: // STATE 11 - dining_philosophers.pml:18 - [fork[((i+1)%3)] = 0] (0:0:1 - 1)
		IfNotBlocked
		reached[0][11] = 1;
		(trpt+1)->bup.oval = ((int)now.fork[ Index(((((int)((P0 *)_this)->i)+1)%3), 3) ]);
		now.fork[ Index(((((P0 *)_this)->i+1)%3), 3) ] = 0;
#ifdef VAR_RANGES
		logval("fork[((Philosopher:i+1)%3)]", ((int)now.fork[ Index(((((int)((P0 *)_this)->i)+1)%3), 3) ]));
#endif
		;
		_m = 3; goto P999; /* 0 */
	case 18: // STATE 16 - dining_philosophers.pml:30 - [-end-] (0:0:0 - 1)
		IfNotBlocked
		reached[0][16] = 1;
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

