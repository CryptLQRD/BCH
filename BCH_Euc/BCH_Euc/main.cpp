// ------------------------------------------------------------------------
//        File: bch_euc.c
//        Date: April 3, 2002
// Description: An encoder/decoder for binary BCH codes
//              Error correction using the EUCLIDEAN ALGORITHM
// ------------------------------------------------------------------------
// This program is complementary material for the book:
//
// R.H. Morelos-Zaragoza, The Art of Error Correcting Coding, Wiley, 2002.
//
// ISBN 0471 49581 6
//
// This and other programs are available at http://the-art-of-ecc.com
//
// You may use this program for academic and personal purposes only. 
// If this program is used to perform simulations whose results are 
// published in a journal or book, please refer to the book above.
//
// The use of this program in a commercial product requires explicit 
// written permission from the author. The author is not responsible or 
// liable for damage or loss that may be caused by the use of this program. 
//
// Copyright (c) 2002. Robert H. Morelos-Zaragoza. All rights reserved.
// ------------------------------------------------------------------------

#include <math.h>
#include <stdio.h>
#include <stack>
#include <cstdlib>
#include <iostream>
#include "stdlib.h"
#include "stdio.h"

using namespace  std;

int             m, n, length, k, t, d;
int             p[21];
int             alpha_to[1048576], index_of[1048576], g[548576];
//todo: падает на объ€влении больших массивов
//-------------------------------------------------------------------//
//int * alpha_to = new int[1048576];



//int             index_of[1048576], g[548576];
//-------------------------------------------------------------------//

int             recd[1048576], data[1048576], bb[548576];
int             seed;
int             numerr, errpos[1024], decerror = 0;


void read_p()
/*
*	Read m, the degree of a primitive polynomial p(x) used to compute the
*	Galois field GF(2**m). Get precomputed coefficients p[] of p(x). Read
*	the code length.
*/
{
	int			i, ninf;

	printf("\nEnter a value of m such that the code length is\n");
	printf("2**(m-1) - 1 < length <= 2**m - 1\n\n");
	do {
		printf("Enter m (between 2 and 20): ");
		scanf_s("%d", &m);
	} while (!(m > 1) || !(m < 21));
	for (i = 1; i < m; i++)
		p[i] = 0;
	p[0] = p[m] = 1;
	if (m == 2)			p[1] = 1;
	else if (m == 3)	p[1] = 1;
	else if (m == 4)	p[1] = 1;
	else if (m == 5)	p[2] = 1;
	else if (m == 6)	p[1] = 1;
	else if (m == 7)	p[1] = 1;
	else if (m == 8)	p[4] = p[5] = p[6] = 1;
	else if (m == 9)	p[4] = 1;
	else if (m == 10)	p[3] = 1;
	else if (m == 11)	p[2] = 1;
	else if (m == 12)	p[3] = p[4] = p[7] = 1;
	else if (m == 13)	p[1] = p[3] = p[4] = 1;
	else if (m == 14)	p[1] = p[11] = p[12] = 1;
	else if (m == 15)	p[1] = 1;
	else if (m == 16)	p[2] = p[3] = p[5] = 1;
	else if (m == 17)	p[3] = 1;
	else if (m == 18)	p[7] = 1;
	else if (m == 19)	p[1] = p[5] = p[6] = 1;
	else if (m == 20)	p[3] = 1;
	printf("p(x) = ");
	n = 1;
	for (i = 0; i <= m; i++) {
		n *= 2;
		printf("%1d", p[i]);
	}
	printf("\n");
	n = n / 2 - 1;
	ninf = (n + 1) / 2 - 1;
	do  {
		printf("Enter code length (%d < length <= %d): ", ninf, n);
		scanf_s("%d", &length);
	} while (!((length <= n) && (length > ninf)));
}


void generate_gf()
/*
* Generate field GF(2**m) from the irreducible polynomial p(X) with
* coefficients in p[0]..p[m].
*
* Lookup tables:
*   index->polynomial form: alpha_to[] contains j=alpha^i;
*   polynomial form -> index form:	index_of[j=alpha^i] = i
*
* alpha=2 is the primitive element of GF(2**m)
*/
{
	register int    i, mask;

	mask = 1;
	alpha_to[m] = 0;
	for (i = 0; i < m; i++) {
		alpha_to[i] = mask;
		index_of[alpha_to[i]] = i;
		if (p[i] != 0)
			alpha_to[m] ^= mask;
		mask <<= 1;
	}
	index_of[alpha_to[m]] = m;
	mask >>= 1;
	for (i = m + 1; i < n; i++) {
		if (alpha_to[i - 1] >= mask)
			alpha_to[i] = alpha_to[m] ^ ((alpha_to[i - 1] ^ mask) << 1);
		else
			alpha_to[i] = alpha_to[i - 1] << 1;
		index_of[alpha_to[i]] = i;
	}
	index_of[0] = -1;
}


void gen_poly()
/*
* Compute the generator polynomial of a binary BCH code. Fist generate the
* cycle sets modulo 2**m - 1, cycle[][] =  (i, 2*i, 4*i, ..., 2^l*i). Then
* determine those cycle sets that contain integers in the set of (d-1)
* consecutive integers {1..(d-1)}. The generator polynomial is calculated
* as the product of linear factors of the form (x+alpha^i), for every i in
* the above cycle sets.
*/
{
	register int	ii, jj, ll, kaux;
	register int	test, aux, nocycles, root, noterms, rdncy;
	int             cycle[1024][21], size[1024], min[1024], zeros[1024];

	/* Generate cycle sets modulo n, n = 2**m - 1 */
	cycle[0][0] = 0;
	size[0] = 1;
	cycle[1][0] = 1;
	size[1] = 1;
	jj = 1;			/* cycle set index */
	if (m > 9)  {
		printf("Computing cycle sets modulo %d\n", n);
		printf("(This may take some time)...\n");
	}
	do {
		/* Generate the jj-th cycle set */
		ii = 0;
		do {
			ii++;
			cycle[jj][ii] = (cycle[jj][ii - 1] * 2) % n;
			size[jj]++;
			aux = (cycle[jj][ii] * 2) % n;
		} while (aux != cycle[jj][0]);
		/* Next cycle set representative */
		ll = 0;
		do {
			ll++;
			test = 0;
			for (ii = 1; ((ii <= jj) && (!test)); ii++)
				/* Examine previous cycle sets */
				for (kaux = 0; ((kaux < size[ii]) && (!test)); kaux++)
					if (ll == cycle[ii][kaux])
						test = 1;
		} while ((test) && (ll < (n - 1)));
		if (!(test)) {
			jj++;	/* next cycle set index */
			cycle[jj][0] = ll;
			size[jj] = 1;
		}
	} while (ll < (n - 1));
	nocycles = jj;		/* number of cycle sets modulo n */

	printf("Enter the error correcting capability, t: ");
	scanf_s("%d", &t);

	d = 2 * t + 1;

	/* Search for roots 1, 2, ..., d-1 in cycle sets */
	kaux = 0;
	rdncy = 0;
	for (ii = 1; ii <= nocycles; ii++) {
		min[kaux] = 0;
		test = 0;
		for (jj = 0; ((jj < size[ii]) && (!test)); jj++)
			for (root = 1; ((root < d) && (!test)); root++)
				if (root == cycle[ii][jj])  {
					test = 1;
					min[kaux] = ii;
				}
		if (min[kaux]) {
			rdncy += size[min[kaux]];
			kaux++;
		}
	}
	noterms = kaux;
	kaux = 1;
	for (ii = 0; ii < noterms; ii++)
		for (jj = 0; jj < size[min[ii]]; jj++) {
			zeros[kaux] = cycle[min[ii]][jj];
			kaux++;
		}

	k = length - rdncy;

	if (k < 0)
	{
		printf("Parameters invalid!\n");
		exit(0);
	}

	printf("This is a (%d, %d, %d) binary BCH code\n", length, k, d);

	/* Compute the generator polynomial */
	g[0] = alpha_to[zeros[1]];
	g[1] = 1;		/* g(x) = (X + zeros[1]) initially */
	for (ii = 2; ii <= rdncy; ii++) {
		g[ii] = 1;
		for (jj = ii - 1; jj > 0; jj--)
			if (g[jj] != 0)
				g[jj] = g[jj - 1] ^ alpha_to[(index_of[g[jj]] + zeros[ii]) % n];
			else
				g[jj] = g[jj - 1];
		g[0] = alpha_to[(index_of[g[0]] + zeros[ii]) % n];
	}
	printf("Generator polynomial:\ng(x) = ");
	for (ii = 0; ii <= rdncy; ii++) {
		printf("%d", g[ii]);
		if (ii && ((ii % 50) == 0))
			printf("\n");
	}
	printf("\n");
}


void
encode_bch()
/*
* Compute redundacy bb[], the coefficients of b(x). The redundancy
* polynomial b(x) is the remainder after dividing x^(length-k)*data(x)
* by the generator polynomial g(x).
*/
{
	register int    i, j;
	register int    feedback;
	for (i = 0; i < length - k; i++)
		bb[i] = 0;
	for (i = k - 1; i >= 0; i--) {
		feedback = data[i] ^ bb[length - k - 1];
		if (feedback != 0) {
			for (j = length - k - 1; j > 0; j--)
				if (g[j] != 0)
					bb[j] = bb[j - 1] ^ feedback;
				else
					bb[j] = bb[j - 1];
			bb[0] = g[0] && feedback;
		}
		else {
			for (j = length - k - 1; j > 0; j--)
				bb[j] = bb[j - 1];
			bb[0] = 0;
		}
	}
}


void
decode_bch()
{
	register int i, j, u, q, t2, count = 0, syn_error = 0;
	//int elp[1026][1024], l[1], s[1025];
	//todo: падает на объ€влении elp
	//-------------------------------------------------------------------//
	int ** elp = (int **)new int[1024];
	for (int i = 0; i < 1024; i++) elp[i] = new int[1026];
	//ƒ—: возможно, 1024 и 1026 перепутаны местами (но это не точно)
	int  l[1], s[1025];
	//-------------------------------------------------------------------//



	int root[200], loc[200], err[1024], reg[201];
	int qt[513], r[129][513];
	int b[12][513];
	int degr[129], degb[129];
	int temp, aux[513];

	t2 = 2 * t;

	/* Compute the syndromes */
	printf("S(x) = ");
	for (i = 1; i <= t2; i++) {
		s[i] = 0;
		for (j = 0; j < length; j++)
			if (recd[j] != 0)
				s[i] ^= alpha_to[(i * j) % n];
		if (s[i] != 0)
			syn_error = 1; /* set error flag if non-zero syndrome */
		/* convert syndrome from polynomial form to index form  */
		s[i] = index_of[s[i]];
		printf("%3d ", s[i]);
	}
	printf("\n");

	if (syn_error)
	{
		//
		// Compute the error location polynomial with the Euclidean algorithm
		// 

		for (i = 0; i <= d; i++) {
			r[0][i] = 0;
			r[1][i] = 0;
			b[0][i] = 0;
			b[1][i] = 0;
			qt[i] = 0;
		}

		b[1][0] = 1; degb[0] = 0; degb[1] = 0;

		r[0][d] = 1; // x^{2t+1}
		degr[0] = d;

		//todo: experiment
		//for (i = 0; i <= t2; i++)
		//-------------------------------------------------------------------//
		for (i = 1; i <= t2; i++)
			//-------------------------------------------------------------------//
		{
			if (s[i] != -1) {
				r[1][i] = alpha_to[s[i]];
				degr[1] = i;
			}
			else
				r[1][i] = 0;
		}

		j = 1;

		if ((degr[0] - degr[1]) <= t) {

			do {

				j++;

				printf("\n************************  j=%3d\n", j);
				// ----------------------------------------
				// Apply long division to r[j-2] and r[j-1]
				// ----------------------------------------

				// Clean r[j]
				for (i = 0; i <= d; i++) r[j][i] = 0;

				for (i = 0; i <= degr[j - 2]; i++)
					r[j][i] = r[j - 2][i];
				degr[j] = degr[j - 2];

				temp = degr[j - 2] - degr[j - 1];
				for (i = temp; i >= 0; i--) {
					u = degr[j - 1] + i;
					if (degr[j] == u)
					{
						if (r[j][degr[j]] && r[j - 1][degr[j - 1]])
							qt[i] = alpha_to[(index_of[r[j][degr[j]]]
							+ n - index_of[r[j - 1][degr[j - 1]]]) % n];

						//printf("r[j][degr[j]]] = %d,  r[j-1][degr[j-1]] = %d\n",
						//index_of[r[j][degr[j]]], index_of[r[j-1][degr[j-1]]]);
						printf("\nqt[%d]=%d\n", i, index_of[qt[i]]);

						for (u = 0; u <= d; u++) aux[u] = 0;

						temp = degr[j - 1];
						for (u = 0; u <= temp; u++)
							if (qt[i] && r[j - 1][u])
								aux[u + i] = alpha_to[(index_of[qt[i]] + index_of[r[j - 1][u]]) % n];
							else
								aux[u + i] = 0;

						printf("r    = ");
						for (u = 0; u <= degr[j]; u++) printf("%4d ", index_of[r[j][u]]);
						printf("\n");
						printf("aux  = ");
						for (u = 0; u <= degr[j - 1] + i; u++) printf("%4d ", index_of[aux[u]]);
						printf("\n");

						for (u = 0; u <= degr[j]; u++)
							r[j][u] ^= aux[u];
						u = d;
						while (!r[j][u] && (u > 0)) u--;
						degr[j] = u;
					}
					else
						qt[i] = 0;

					printf("r    = ");
					for (u = 0; u <= degr[j]; u++) printf("%4d ", index_of[r[j][u]]);
					printf("\n");

				}

				printf("\nqt = ", j);
				temp = degr[j - 2] - degr[j - 1];
				for (i = 0; i <= temp; i++) printf("%4d ", index_of[qt[i]]);
				printf("\nr = ");
				for (i = 0; i <= degr[j]; i++) printf("%4d ", index_of[r[j][i]]);
				printf("\nb = ");

				// Compute b(x)

				for (i = 0; i <= d; i++)
					aux[i] = 0;

				temp = degr[j - 2] - degr[j - 1];
				for (i = 0; i <= temp; i++)
					for (u = 0; u <= degb[j - 1]; u++)
						if (qt[i] && b[j - 1][u])
							aux[i + u] ^= alpha_to[(index_of[qt[i]] + index_of[b[j - 1][u]]) % n];

				for (i = 0; i <= d; i++)
					b[j][i] = b[j - 2][i] ^ aux[i];

				u = d;
				while (!b[j][u] && (u > 0)) u--;
				degb[j] = u;

				for (i = 0; i <= degb[j]; i++) printf("%4d ", index_of[b[j][i]]);
				printf("\n");

			} while (degr[j] > t);

		}

		//u = 1;
		//temp = degb[j];
		//// Normalize error locator polynomial
		//for (i = 0; i <= temp; i++) {
		//	elp[u][i] = alpha_to[(index_of[b[j][i]] - index_of[b[j][0]] + n) % n];
		//}
		//l[u] = temp;

		//if (l[u] <= t) {
		//	/* put elp into index form */
		//	for (i = 0; i <= l[u]; i++)
		//		elp[u][i] = index_of[elp[u][i]];

		//	printf("sigma(x) = ");
		//	for (i = 0; i <= l[u]; i++)
		//		printf("%3d ", elp[u][i]);
		//	printf("\n");
		//	printf("Roots: ");

		//	/* Chien search: find roots of the error location polynomial */
		//	for (i = 1; i <= l[u]; i++)
		//		reg[i] = elp[u][i];
		//	count = 0;
		//	for (i = 1; i <= n; i++) {
		//		q = 1;
		//		for (j = 1; j <= l[u]; j++)
		//			if (reg[j] != -1) {
		//				reg[j] = (reg[j] + j) % n;
		//				q ^= alpha_to[reg[j]];
		//			}
		//		if (!q) {
		//			root[count] = i;
		//			loc[count] = n - i;
		//			count++;
		//			printf("%3d ", n - i);
		//		}
		//	}
		//	printf("\n");

		//	if (count == l[u])
		//		/* no. roots = degree of elp hence <= t errors */
		//		for (i = 0; i < l[u]; i++)
		//			recd[loc[i]] ^= 1;
		//	else
		//		printf("Incomplete decoding: errors detected\n");
		//}
	}
}



void main() {
	int             i;

	read_p();               /* Read m */
	generate_gf();          /* Construct the Galois Field GF(2**m) */
	gen_poly();             /* Compute the generator polynomial of BCH code */

	/* Randomly generate DATA */
	seed = 131073;
	srand(seed);
	for (i = 0; i < k; i++)
		data[i] = (rand() & 65536) >> 16;

	encode_bch();           /* encode data */

	/*
	* recd[] are the coefficients of c(x) = x**(length-k)*data(x) + b(x)
	*/
	for (i = 0; i < length - k; i++)
		recd[i] = bb[i];
	for (i = 0; i < k; i++)
		recd[i + length - k] = data[i];
	printf("Code polynomial:\nc(x) = ");
	for (i = 0; i < length; i++) {
		printf("%1d", recd[i]);
		if (i && ((i % 50) == 0))
			printf("\n");
	}
	printf("\n");

	printf("Enter the number of errors:\n");
	scanf_s("%d", &numerr);	/* CHANNEL errors */
	printf("Enter error locations (integers between");
	printf(" 0 and %d): ", length - 1);
	/*
	* recd[] are the coefficients of r(x) = c(x) + e(x)
	*/
	for (i = 0; i < numerr; i++)
		scanf_s("%d", &errpos[i]);
	if (numerr)
		for (i = 0; i < numerr; i++)
			recd[errpos[i]] ^= 1;
	printf("r(x) = ");
	for (i = 0; i < length; i++) {
		printf("%1d", recd[i]);
		if (i && ((i % 50) == 0))
			printf("\n");
	}
	printf("\n");
	system("pause");
	decode_bch();             /* DECODE received codeword recv[] */

	/*
	* print out original and decoded data
	*/
	printf("Results:\n");
	printf("original data  = ");
	for (i = 0; i < k; i++) {
		printf("%1d", data[i]);
		if (i && ((i % 50) == 0))
			printf("\n");
	}
	printf("\nrecovered data = ");
	for (i = length - k; i < length; i++) {
		printf("%1d", recd[i]);
		if ((i - length + k) && (((i - length + k) % 50) == 0))
			printf("\n");
	}
	printf("\n");

	/*
	* DECODING ERRORS? we compare only the data portion
	*/
	for (i = length - k; i < length; i++)
		if (data[i - length + k] != recd[i])
			decerror++;
	if (decerror)
		printf("There were %d decoding errors in message positions\n", decerror);
	else
		printf("Succesful decoding\n");
	system("pause");
}
