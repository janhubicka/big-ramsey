/* This program generates poset types as given by Definition 1 of the paper.
   Insetead of L,X,R letters L,O,R used to make output happier and also
   easily sorted alphabetically in ascii. 

   Output is easier to read when _ is replaced by a new line.  However before
   replacement there is one type per line which makes it easy to process
   by sort and grep.   */
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

/* Maximum number of vertices of diaries generated.  */
#define MAXLEAFS 3

/* Set to 1 to print debug info on the search.  */
static int debug = 0;
/* Extra anal checking. */
static int analcheck = 0;

/* Limits on various array sizes derived from MAXLEAFS.  */
#define MAXTYPES MAXLEAFS
/* Number of branching + number of new events + number of leavs + 1 for 0 + 1 for backup.  */
#define MAXLENGTH (MAXLEAFS-1 + MAXLEAFS * (MAXLEAFS - 1) /2 + MAXLEAFS + 2)


/* The following datastructures holds that status of the exhastive search.  */

/* Type of the level (b=branching; l=leaf; p=new perp; <=new preceq.  */
static char lev[MAXLENGTH];
/* Word representing each type.  */
static char types[MAXTYPES][MAXLENGTH + 1];
/* Number of relations each type is in; used to speed up testing if given
   type can be leaf.  */
static int relations[MAXTYPES];
/* Words representing leafs.  */
static char leafs[MAXLEAFS][MAXLENGTH + 1];


static int length, ntypes, nleafs;

static void dobranch ();
static void doperp ();
static void doprec ();
static void doleaf ();
static void print_type ();

/* \ltlex from the paper.  */
static int
ltlex (char *s1, char *s2)
{
  int i;
  for (i = 0; s1[i] && s2[i]; i++)
    {
      if (s1[i] < s2[i])
	return 1;
      if (s1[i] > s2[i])
	return 0;
    }
  return 0;
}

/* \prec from the paper.  */
static int
prec (char *s1, char *s2)
{
  int i;
  for (i = 0; s1[i] && s2[i]; i++)
    {
      if (s1[i] > s2[i])
	return 0;
      if (s1[i] == 'L' && s2[i] == 'R')
	return 1;
    }
  return 0;
}

/* \perp from the paper.  */
static int
perp (char *s1, char *s2)
{
  int i;
  int f1 = 0, f2 = 0;
  for (i = 0; s1[i] && s2[i]; i++)
    {
      if (s1[i] < s2[i])
	f1 = 1;
      if (s1[i] > s2[i])
	f2 = 1;
      if (f1 && f2)
	return 1;
    }
  return 0;
}

/* Compatibility conditions from the paper.  */
static int
compatible (char *s1, char *s2)
{
  int i;
  int c = -1;
  for (i = 0; s1[i] && s2[i] && c == -1; i++)
    {
      if (s1[i]=='L' && s2[i]=='R')
	c = 0;
      if (s1[i]=='R' && s2[i]=='L')
	c = 1;
    }
  if (c == -1)
    return 1;
  if (c==0)
    for (i = 0; s1[i] && s2[i]; i++)
      if (s1[i] > s2[i])
	return 0;
  if (c==1)
    for (i = 0; s1[i] && s2[i]; i++)
      if (s1[i] < s2[i])
	return 0;
  return 1;
}

/* Print current state of the search.  */
static void
printstate ()
{
  printf ("Seq:%s\n", lev);
  for (int i = 0; i < ntypes; i++)
    printf ("Type %s\n", types[i]);
  for (int i = 0; i < nleafs; i++)
    printf ("Leaf %s\n", leafs[i]);
  printf ("\n");
}


/* Count number of prec and perp relations.
   Useful for verification of diary consistency.  */
static void
counts (int *preccount, int *perpcount)
{
  int nrelations[MAXTYPES];
  *preccount = 0;
  *perpcount = 0;
  for (int i = 0; i < ntypes; i++)
    nrelations[i]=0;
  for (int i = 0; i < ntypes; i++)
    {
      if (strlen (types[i]) != length)
	{
	  printf ("Error length %i %i\n", i - 1, i);
	  printstate ();
	  exit (1);
	}
      if (i > 0 && !ltlex (types[i - 1], types[i]))
	{
	  printf ("Error %i %i\n", i - 1, i);
	  printstate ();
	  exit (1);
	}
      for (int j = i + 1; j < ntypes; j++)
	{
	  if (prec (types[i], types[j]))
	    (*preccount)++, nrelations[i]++, nrelations[j]++;
	  else if (perp (types[i], types[j]))
	    (*perpcount)++, nrelations[i]++, nrelations[j]++;
	}
    }
  for (int i = 0; i < ntypes; i++)
    if (relations[i] != nrelations[i])
      abort ();
}

/* Main recursive search.  */
static void
recurse ()
{
  if (length >= MAXLENGTH)
    return;
  if (debug)
    printstate ();
  int c1, c2;

  /* Try to make next level leaf.  */
  if (analcheck)
    counts (&c1, &c2);
  doleaf ();

  /* Try to make next level branch.  */
  if (analcheck)
    counts (&c1, &c2);
  dobranch ();

  /* Try to make next level perp.  */
  if (analcheck)
    counts (&c1, &c2);
  doperp ();

  /* Try to make next level prec.  */
  if (analcheck)
    counts (&c1, &c2);
  doprec ();
}

/* Try to do branching.  */
static void
dobranch ()
{
  char bckuptypes[MAXTYPES][MAXLENGTH + 1];
  int bckuprelations[MAXTYPES];
  int c1, c2;

  /* First see if branching is desired.  */
  if (ntypes >= MAXTYPES || ntypes + nleafs >= MAXLEAFS)
    return;
  counts (&c1, &c2);
  if (length + (ntypes * (ntypes - 1)) - c1 - c2 >= MAXLENGTH)
    return;

  /* Make local copy of state so it can be easily restored.  */
  memcpy (bckuptypes, types, sizeof (types));
  memcpy (bckuprelations, relations, sizeof (relations));

  /* Try to branch each type.  */
  for (int i = 0; i < ntypes; i++)
    {
      /* Insert copy of the type and add R.  */
      for (int j = ntypes; j > i; j--)
	{
	  strcpy (types[j], types[j - 1]);
	  relations[j] = relations[j - 1];
	  types[j][length] = 'R';
	}
      /* Extend remainign types by O.  */
      for (int k = 0; k <= i; k++)
	types[k][length] = 'O';

      /* Next level is branching.  */
      lev[length] = 'b';

      /* Update state and recurse.  */
      ntypes++;
      length++;
      for (int k = 0; k < i; k++)
	if (prec (types[k],types[i]) || perp (types[k],types[i]))
	  relations[k]++;
      for (int k = i+2; k < ntypes; k++)
	if (prec (types[i],types[k]) || perp (types[i],types[k]))
	  relations[k]++;
      recurse ();

      /* Restore previous state.  */
      ntypes--;
      length--;
      lev[length] = 0;
      memcpy (types, bckuptypes, sizeof (types));
      memcpy (relations, bckuprelations, sizeof (relations));
    }
}

/* Try to add perp.  */
static void
doperp ()
{
  int bckup = 0;
  char bckuptypes[MAXTYPES][MAXLENGTH + 1];
  int bckuprelations[MAXTYPES];

  int c1, c2, cc1, cc2;
  if (analcheck)
    counts (&c1, &c2);

  /* Consider every pair of types and see if new perp can be added
     according to Definition 1.  */
  for (int i = 0; i < ntypes; i++)
    for (int j = i + 1; j < ntypes; j++)
      {
	/* Types needs to be unrelated.  */
	if (!perp (types[i], types[j]) && !prec (types[i], types[j]))
	  {
	    int k;

	    /* Verify conditon (A)  */
	    for (k = i + 1; k < j; k++)
	      if (!perp (types[i], types[k]) && !perp (types[k], types[j]))
		break;
	    if (j != k)
	      continue;

	    if (!bckup)
	      memcpy (bckuptypes, types, sizeof (types));
	    bckup=1;

	    /* Update types producing new perp.  */
	    for (k = 0; k < i; k++)
	      types[k][length] = 'O';
	    types[i][length] = 'R';
	    for (k = i + 1; k < j; k++)
	      types[k][length] = perp (types[i], types[k]) ? 'O' : 'R';
	    types[j][length] = 'O';
	    for (k = j + 1; k < ntypes; k++)
	      types[k][length] = 'R';
	    lev[length] = 'p';
	    length++;
	    relations[i]++;
	    relations[j]++;

	    /* Check that really preciosely one perp was added.  */
	    if (analcheck)
	      {
		counts (&cc1, &cc2);
		if (cc1 != c1 || cc2 != c2 + 1)
		  {
		    printf ("Error prep %i %i %i %i\n", c1, cc1, c2, cc2);
		    printstate ();
		    exit (2);
		  }
	      }

	    recurse ();

	    /* Restore previous state.  */
	    relations[i]--;
	    relations[j]--;
	    length--;
	    lev[length] = 0;
	    memcpy (types, bckuptypes, sizeof (types));
	  }
      }
}

static void
doprec ()
{
  char bckuptypes[MAXTYPES][MAXLENGTH + 1];
  int bckup = 0;

  int c1, c2, cc1, cc2;
  if (analcheck)
    counts (&c1, &c2);

  /* Consider every pair of types and see if new prec can be added
     according to Definition 1.  */
  for (int i = 0; i < ntypes; i++)
    for (int j = i + 1; j < ntypes; j++)
      {
	/* Types has to be unrelated.   */
	if (!perp (types[i], types[j]) && !prec (types[i], types[j]))
	  {
	    int k;

	    /* Check (B1) and (B2) of the paper.  */
	    for (k = 0; k < i; k++)
	      if (!perp (types[k], types[i]) && !prec (types[k], types[j]))
		break;
	    if (k != i)
	      continue;
	    for (k = j + 1; k < ntypes; k++)
	      if (!perp (types[j], types[k]) && !prec (types[i], types[k]))
		break;
	    if (k != ntypes)
	      continue;
	    if (!bckup)
	      memcpy (bckuptypes, types, sizeof (types));
	    bckup=1;

	    /* Update types.  */
	    for (k = 0; k < i; k++)
	      types[k][length] = perp (types[k], types[i]) ? 'O' : 'L';
	    types[i][length] = 'L';
	    for (k = i + 1; k < j; k++)
	      types[k][length] = 'O';
	    types[j][length] = 'R';
	    for (k = j + 1; k < ntypes; k++)
	      types[k][length] = perp (types[j], types[k]) ? 'O' : 'R';
	    lev[length] = '<';
	    length++;
	    relations[i]++;
	    relations[j]++;

	    /* Check that really preciosely one prec was added.  */
	    if (analcheck)
	      {
		counts (&cc1, &cc2);
		if (cc1 != c1 + 1 || cc2 != c2)
		  {
		    printf ("Error prec %i %i %i %i\n", c1, cc1, c2, cc2);
		    printstate ();
		    exit (2);
		  }
	      }

	    recurse ();

	    /* Restore previous state.  */
	    relations[i]--;
	    relations[j]--;
	    length--;
	    lev[length] = 0;
	    memcpy (types, bckuptypes, sizeof (types));
	  }
      }
}

/* Try to add leaf level.  */
static void
doleaf ()
{
  if (nleafs == MAXLEAFS || !ntypes)
    return;
  char bckuptypes[MAXTYPES][MAXLENGTH + 1];
  int bckuprelations[MAXTYPES];
  int bckup = 0;
  for (int i = 0; i < ntypes; i++)
    {
      int j;

      /* See if type is already related to every other type.  */
      if (relations[i] != ntypes - 1)
	continue;
      if (!bckup)
	{
	  memcpy (bckuptypes, types, sizeof (types));
          memcpy (bckuprelations, relations, sizeof (relations));
	}
      bckup = 1;
      strcpy (leafs[nleafs], types[i]);
      nleafs++;
      lev[length] = 'l';

      /* If this is last leaf print the type generated.  */
      if (ntypes == 1)
	{
	  print_type ();
	  nleafs--;
	  lev[length] = 0;
	  continue;
	}

      /* Otherwise update state.  */
      for (int k = 0; k < i; k++)
	{
	  relations[k]--;
	  types[k][length] = 'O';
	}
      for (int k = i; k < ntypes - 1; k++)
	{
	  relations[k] = relations[k + 1] - 1;
	  strcpy (types[k], types[k + 1]);
	  types[k][length] = 'O';
	}
      ntypes--;
      length++;

      recurse ();

      /* Restore previous state.  */
      length--;
      nleafs--;
      ntypes++;
      lev[length] = 0;
      memcpy (types, bckuptypes, sizeof (types));
      memcpy (relations, bckuprelations, sizeof (relations));
    }
}

/* Print type.  */
static void
print_type ()
{
  printf ("_Adj. matrix: ");
  for (int i = 1; i < nleafs; i++)
    {
      for (int j = 0; j < i; j++)
	printf (prec (leafs[i], leafs[j]) ? "l" :
		prec (leafs[j], leafs[i]) ? "g" : "i");
      if (i + 1 < nleafs)
        printf ("_             ");
    }
  printf ("_level types: %s", lev);

  int leafmap[MAXLEAFS];
  int leafmap2[MAXLEAFS];

  /* Sort leafs lexicographically.  */
  for (int i = 0; i < nleafs; i++)
    {
      int c = 0;
      for (int j = 0; j < nleafs; j++)
	if (i != j && ltlex (leafs[j], leafs[i]))
	  c++;
      leafmap[c] = i;
      leafmap2[i] = c;
    }
  for (int i = 0; i < nleafs; i++)
    printf ("_vertex   %2i: %s (lexpos %i)", i, leafs[i], leafmap2[i]);

  printf ("\n");
}

int
main ()
{
  ntypes = 1;
  recurse ();
  return 0;
}
