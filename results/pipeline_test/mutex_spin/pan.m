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

		 /* CLAIM progress */
	case 3: // STATE 1 - _spin_nvr.tmp:12 - [(!((critical==1)))] (0:0:0 - 1)
		
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
		reached[3][1] = 1;
		if (!( !((((int)now.critical)==1))))
			continue;
		_m = 3; goto P999; /* 0 */
	case 4: // STATE 8 - _spin_nvr.tmp:17 - [(!((critical==1)))] (0:0:0 - 1)
		
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
		reached[3][8] = 1;
		if (!( !((((int)now.critical)==1))))
			continue;
		_m = 3; goto P999; /* 0 */
	case 5: // STATE 13 - _spin_nvr.tmp:19 - [-end-] (0:0:0 - 1)
		
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
		reached[3][13] = 1;
		if (!delproc(1, II)) continue;
		_m = 3; goto P999; /* 0 */

		 /* CLAIM mutex */
	case 6: // STATE 1 - _spin_nvr.tmp:3 - [(!((critical<=1)))] (6:0:0 - 1)
		
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
		if (!( !((((int)now.critical)<=1))))
			continue;
		/* merge: assert(!(!((critical<=1))))(0, 2, 6) */
		reached[2][2] = 1;
		spin_assert( !( !((((int)now.critical)<=1))), " !( !((critical<=1)))", II, tt, t);
		/* merge: .(goto)(0, 7, 6) */
		reached[2][7] = 1;
		;
		_m = 3; goto P999; /* 2 */
	case 7: // STATE 10 - _spin_nvr.tmp:8 - [-end-] (0:0:0 - 1)
		
#if defined(VERI) && !defined(NP)
#if NCLAIMS>1
		{	static int reported10 = 0;
			if (verbose && !reported10)
			{	int nn = (int) ((Pclaim *)pptr(0))->_n;
				printf("depth %ld: Claim %s (%d), state %d (line %d)\n",
					depth, procname[spin_c_typ[nn]], nn, (int) ((Pclaim *)pptr(0))->_p, src_claim[ (int) ((Pclaim *)pptr(0))->_p ]);
				reported10 = 1;
				fflush(stdout);
		}	}
#else
		{	static int reported10 = 0;
			if (verbose && !reported10)
			{	printf("depth %d: Claim, state %d (line %d)\n",
					(int) depth, (int) ((Pclaim *)pptr(0))->_p, src_claim[ (int) ((Pclaim *)pptr(0))->_p ]);
				reported10 = 1;
				fflush(stdout);
		}	}
#endif
#endif
		reached[2][10] = 1;
		if (!delproc(1, II)) continue;
		_m = 3; goto P999; /* 0 */

		 /* PROC Process1 */
	case 8: // STATE 1 - mutex.pml:21 - [((lock==0))] (8:0:4 - 1)
		IfNotBlocked
		reached[1][1] = 1;
		if (!((((int)now.lock)==0)))
			continue;
		/* merge: lock = 1(8, 2, 8) */
		reached[1][2] = 1;
		(trpt+1)->bup.ovals = grab_ints(4);
		(trpt+1)->bup.ovals[0] = ((int)now.lock);
		now.lock = 1;
#ifdef VAR_RANGES
		logval("lock", ((int)now.lock));
#endif
		;
		/* merge: critical = (critical+1)(8, 3, 8) */
		reached[1][3] = 1;
		(trpt+1)->bup.ovals[1] = ((int)now.critical);
		now.critical = (((int)now.critical)+1);
#ifdef VAR_RANGES
		logval("critical", ((int)now.critical));
#endif
		;
		/* merge: assert((critical==1))(8, 4, 8) */
		reached[1][4] = 1;
		spin_assert((((int)now.critical)==1), "(critical==1)", II, tt, t);
		/* merge: critical = (critical-1)(8, 5, 8) */
		reached[1][5] = 1;
		(trpt+1)->bup.ovals[2] = ((int)now.critical);
		now.critical = (((int)now.critical)-1);
#ifdef VAR_RANGES
		logval("critical", ((int)now.critical));
#endif
		;
		/* merge: lock = 0(8, 6, 8) */
		reached[1][6] = 1;
		(trpt+1)->bup.ovals[3] = ((int)now.lock);
		now.lock = 0;
#ifdef VAR_RANGES
		logval("lock", ((int)now.lock));
#endif
		;
		/* merge: .(goto)(0, 9, 8) */
		reached[1][9] = 1;
		;
		_m = 3; goto P999; /* 6 */
	case 9: // STATE 11 - mutex.pml:29 - [-end-] (0:0:0 - 1)
		IfNotBlocked
		reached[1][11] = 1;
		if (!delproc(1, II)) continue;
		_m = 3; goto P999; /* 0 */

		 /* PROC Process0 */
	case 10: // STATE 1 - mutex.pml:8 - [((lock==0))] (8:0:4 - 1)
		IfNotBlocked
		reached[0][1] = 1;
		if (!((((int)now.lock)==0)))
			continue;
		/* merge: lock = 1(8, 2, 8) */
		reached[0][2] = 1;
		(trpt+1)->bup.ovals = grab_ints(4);
		(trpt+1)->bup.ovals[0] = ((int)now.lock);
		now.lock = 1;
#ifdef VAR_RANGES
		logval("lock", ((int)now.lock));
#endif
		;
		/* merge: critical = (critical+1)(8, 3, 8) */
		reached[0][3] = 1;
		(trpt+1)->bup.ovals[1] = ((int)now.critical);
		now.critical = (((int)now.critical)+1);
#ifdef VAR_RANGES
		logval("critical", ((int)now.critical));
#endif
		;
		/* merge: assert((critical==1))(8, 4, 8) */
		reached[0][4] = 1;
		spin_assert((((int)now.critical)==1), "(critical==1)", II, tt, t);
		/* merge: critical = (critical-1)(8, 5, 8) */
		reached[0][5] = 1;
		(trpt+1)->bup.ovals[2] = ((int)now.critical);
		now.critical = (((int)now.critical)-1);
#ifdef VAR_RANGES
		logval("critical", ((int)now.critical));
#endif
		;
		/* merge: lock = 0(8, 6, 8) */
		reached[0][6] = 1;
		(trpt+1)->bup.ovals[3] = ((int)now.lock);
		now.lock = 0;
#ifdef VAR_RANGES
		logval("lock", ((int)now.lock));
#endif
		;
		/* merge: .(goto)(0, 9, 8) */
		reached[0][9] = 1;
		;
		_m = 3; goto P999; /* 6 */
	case 11: // STATE 11 - mutex.pml:16 - [-end-] (0:0:0 - 1)
		IfNotBlocked
		reached[0][11] = 1;
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

