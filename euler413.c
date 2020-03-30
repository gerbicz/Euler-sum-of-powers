//
// Written by Robert Gerbicz from Hungary
// Fast search for solutions of the Euler(4,1,3) systems: a^4=b^4+c^4+d^4 by a new method.
//
// The smallest solution is (4,1,3) 422481^4=414560^4+217519^4+95800^4 (Roger Frye, 1988) 
//
// pari programs to generate some tables:
// pari:  f(p)=for(n=0,p-1,print1((n^4)%p,",");if(n%30==29,print()))
// pari:  g(p)=for(n=0,2*p-1,if((n%p==0)||(Mod(n,p)^((p-1)/gcd(4,p-1))==Mod(1,p)),print1("1,"),print1("0,"));if(n%30==29,print()))
//
//
// Modified to use a save file
// Modified to use less memory by a factor of 3.75
// Modified to use less memory and some gain in speed.  // Using 50MB Ram for 2 billion
//

#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <time.h>

#define TIME_INTERVAL 600  // 600 seconds (update interval)

   unsigned int table_size=262144;  // it is enough for Range<2 billion
   unsigned int Range;  // this must be a multiple of 625*16384=10240000
                              // search up to a<Range

   unsigned char complete_search;  // if it is 0 then we're searching only for special solutions
                                    // , where two numbers of b,c,d are divisible by 40
                                    // this is much faster!
                                    // if it is positive then do complete search up to Range
                                      
   unsigned int* R;
   unsigned int* L;
   unsigned int* temp;

   FILE* out;

unsigned int powmod4(unsigned int a, unsigned int p)
{
  unsigned long long int h=a,K=(h*h)%p;
  
  return (K*K)%p;
}

unsigned int powmod(unsigned int a, unsigned int pow, unsigned int p)
{
// return by a^pow modulo p
  unsigned long long int result=1,H=a;
  while(pow>0)  {
         if(pow&1)  result=(result*H)%p;
         H=(H*H)%p;
         pow>>=1;
  }
  
  return result;
}

static unsigned int Bits[] = {
                         0x00000001,0x00000002,0x00000004,0x00000008,
                         0x00000010,0x00000020,0x00000040,0x00000080,
                         0x00000100,0x00000200,0x00000400,0x00000800,
                         0x00001000,0x00002000,0x00004000,0x00008000,
                         0x00010000,0x00020000,0x00040000,0x00080000,
                         0x00100000,0x00200000,0x00400000,0x00800000,
                         0x01000000,0x02000000,0x04000000,0x08000000,
                         0x10000000,0x20000000,0x40000000,0x80000000};

unsigned int single_modinv (unsigned int a, unsigned int modulus)
{ /* start of single_modinv */

  unsigned int ps1, ps2, dividend, divisor, rem, q, t;

  unsigned char parity;

  q = 1;
  rem = a%modulus;
  dividend = modulus;
  divisor = a;
  ps1 = 1;
  ps2 = 0;
  parity = 0;

  while (divisor > 1)
  {
    rem = dividend - divisor;
    t = rem - divisor;
    if (t >= 0) {
      q += ps1;
      rem = t;
      t -= divisor;
      if (t >= 0) {
        q += ps1;
        rem = t;
        t -= divisor;
        if (t >= 0) {
          q += ps1;
          rem = t;
          t -= divisor;
          if (t >= 0) {
            q += ps1;
            rem = t;
            t -= divisor;
            if (t >= 0) {
              q += ps1;
              rem = t;
              t -= divisor;
              if (t >= 0) {
                q += ps1;
                rem = t;
                t -= divisor;
                if (t >= 0) {
                  q += ps1;
                  rem = t;
                  t -= divisor;
                  if (t >= 0) {
                    q += ps1;
                    rem = t;
                    if (rem >= divisor) {
                      q = dividend/divisor;
                      rem = dividend - q * divisor;
                      q *= ps1;
                    }}}}}}}}}
    q += ps2;
    parity = ~parity;
    dividend = divisor;
    divisor = rem;
    ps2 = ps1;
    ps1 = q;
  }

  if(parity==0)
    return (ps1);
  else
    return (modulus - ps1);
} /* end of single_modinv from Mersenneforum.org*/

unsigned int gcd(unsigned int a, unsigned int b)
// return by gcd of a and b
{// fast but speed isn't important for the program.
   unsigned int c;

   while(b>0)  {
      if(a>=b)  {
         a-=b;
         if(a>=b)  {
            a-=b;
            if(a>=b)  {
               a-=b;
               if(a>=b)  {
                  a-=b;
                  if(a>=b)  {
                     a-=b;
                     if(a>=b)  {
                        a-=b;
                        if(a>=b)  {
                           a-=b;
                           if(a>=b)  {
                              a-=b;
                              if(a>=b)  a%=b;
               }}}}}}}}
      c=a,a=b,b=c;
   }
   return a;
}

// (n^4)%p for the smallest primes that are congurent to 1 mod 4, p>5
// as a bouns we use also 7 as an additional prime in the search ( only if it gives speedup )
static unsigned int rem7[7]={
0 , 1 , 2 , 4 , 4 , 2 , 1};
static unsigned int rem13[13]={
0 , 1 , 3 , 3 , 9 , 1 , 9 , 9 , 1 , 9 , 3 , 3 , 1};
static unsigned int rem17[17]={
0 , 1 , 16 , 13 , 1 , 13 , 4 , 4 , 16 , 16 , 4 , 4 , 13 , 1 , 13 ,
16 , 1};
static unsigned int rem29[29]={
0 , 1 , 16 , 23 , 24 , 16 , 20 , 23 , 7 , 7 , 24 , 25 , 1 , 25 , 20 ,
20 , 25 , 1 , 25 , 24 , 7 , 7 , 23 , 20 , 16 , 24 , 23 , 16 , 1};
static unsigned int rem37[37]={
0 , 1 , 16 , 7 , 34 , 33 , 1 , 33 , 26 , 12 , 10 , 26 , 16 , 34 , 10 ,
9 , 9 , 12 , 7 , 7 , 12 , 9 , 9 , 10 , 34 , 16 , 26 , 10 , 12 , 26 ,
33 , 1 , 33 , 34 , 7 , 16 , 1};
static unsigned int rem41[41]={
0 , 1 , 16 , 40 , 10 , 10 , 25 , 23 , 37 , 1 , 37 , 4 , 31 , 25 , 40 ,
31 , 18 , 4 , 16 , 23 , 18 , 18 , 23 , 16 , 4 , 18 , 31 , 40 , 25 , 31 ,
4 , 37 , 1 , 37 , 23 , 25 , 10 , 10 , 40 , 16 , 1};
static unsigned int rem53[53]={
0 , 1 , 16 , 28 , 44 , 42 , 24 , 16 , 15 , 42 , 36 , 13 , 13 , 47 , 44 ,
10 , 28 , 46 , 36 , 47 , 46 , 24 , 49 , 1 , 49 , 15 , 10 , 10 , 15 , 49 ,
1 , 49 , 24 , 46 , 47 , 36 , 46 , 28 , 10 , 44 , 47 , 13 , 13 , 36 , 42 ,
15 , 16 , 24 , 42 , 44 , 28 , 16 , 1};
static unsigned int rem61[61]={
0 , 1 , 16 , 20 , 12 , 15 , 15 , 22 , 9 , 34 , 57 , 1 , 57 , 13 , 47 ,
56 , 22 , 12 , 56 , 25 , 58 , 13 , 16 , 34 , 58 , 42 , 25 , 9 , 20 , 47 ,
42 , 42 , 47 , 20 , 9 , 25 , 42 , 58 , 34 , 16 , 13 , 58 , 25 , 56 , 12 ,
22 , 56 , 47 , 13 , 57 , 1 , 57 , 34 , 9 , 22 , 15 , 15 , 12 , 20 , 16 ,
1};
static unsigned int rem73[73]={
0 , 1 , 16 , 8 , 37 , 41 , 55 , 65 , 8 , 64 , 72 , 41 , 4 , 18 , 18 ,
36 , 55 , 9 , 2 , 16 , 57 , 9 , 72 , 32 , 64 , 2 , 69 , 1 , 69 , 57 ,
65 , 71 , 4 , 36 , 71 , 37 , 32 , 32 , 37 , 71 , 36 , 4 , 71 , 65 , 57 ,
69 , 1 , 69 , 2 , 64 , 32 , 72 , 9 , 57 , 16 , 2 , 9 , 55 , 36 , 18 ,
18 , 4 , 41 , 72 , 64 , 8 , 65 , 55 , 41 , 37 , 8 , 16 , 1};
static unsigned int rem89[89]={
0 , 1 , 16 , 81 , 78 , 2 , 50 , 87 , 2 , 64 , 32 , 45 , 88 , 81 , 57 ,
73 , 32 , 39 , 45 , 25 , 67 , 16 , 8 , 25 , 73 , 4 , 50 , 22 , 22 , 87 ,
11 , 57 , 67 , 85 , 1 , 85 , 8 , 88 , 44 , 64 , 4 , 11 , 78 , 44 , 39 ,
39 , 44 , 78 , 11 , 4 , 64 , 44 , 88 , 8 , 85 , 1 , 85 , 67 , 57 , 11 ,
87 , 22 , 22 , 50 , 4 , 73 , 25 , 8 , 16 , 67 , 25 , 45 , 39 , 32 , 73 ,
57 , 81 , 88 , 45 , 32 , 64 , 2 , 87 , 50 , 2 , 78 , 81 , 16 , 1};
static unsigned int rem97[97]={
0 , 1 , 16 , 81 , 62 , 43 , 35 , 73 , 22 , 62 , 9 , 91 , 75 , 43 , 4 ,
88 , 61 , 4 , 22 , 50 , 47 , 93 , 1 , 93 , 36 , 6 , 9 , 75 , 64 , 54 ,
50 , 81 , 6 , 96 , 64 , 35 , 61 , 24 , 24 , 88 , 73 , 54 , 33 , 36 , 16 ,
47 , 33 , 96 , 91 , 91 , 96 , 33 , 47 , 16 , 36 , 33 , 54 , 73 , 88 , 24 ,
24 , 61 , 35 , 64 , 96 , 6 , 81 , 50 , 54 , 64 , 75 , 9 , 6 , 36 , 93 ,
1 , 93 , 47 , 50 , 22 , 4 , 61 , 88 , 4 , 43 , 75 , 91 , 9 , 62 , 22 ,
73 , 35 , 43 , 62 , 81 , 16 , 1};
static unsigned int rem101[101]={
0 , 1 , 16 , 81 , 54 , 19 , 84 , 78 , 56 , 97 , 1 , 97 , 31 , 79 , 36 ,
24 , 88 , 95 , 37 , 31 , 16 , 56 , 37 , 71 , 92 , 58 , 52 , 80 , 71 , 79 ,
81 , 78 , 95 , 80 , 5 , 68 , 87 , 5 , 92 , 36 , 54 , 84 , 88 , 52 , 87 ,
25 , 25 , 68 , 58 , 24 , 19 , 19 , 24 , 58 , 68 , 25 , 25 , 87 , 52 , 88 ,
84 , 54 , 36 , 92 , 5 , 87 , 68 , 5 , 80 , 95 , 78 , 81 , 79 , 71 , 80 ,
52 , 58 , 92 , 71 , 37 , 56 , 16 , 31 , 37 , 95 , 88 , 24 , 36 , 79 , 31 ,
97 , 1 , 97 , 56 , 78 , 84 , 19 , 54 , 81 , 16 , 1};
static unsigned int rem109[109]={
0 , 1 , 16 , 81 , 38 , 80 , 97 , 3 , 63 , 21 , 81 , 35 , 26 , 3 , 48 ,
49 , 27 , 27 , 9 , 66 , 97 , 25 , 15 , 38 , 89 , 78 , 48 , 66 , 5 , 89 ,
21 , 73 , 105 , 1 , 105 , 22 , 35 , 15 , 75 , 25 , 26 , 45 , 73 , 16 , 22 ,
45 , 63 , 78 , 7 , 9 , 49 , 7 , 5 , 80 , 75 , 75 , 80 , 5 , 7 , 49 ,
9 , 7 , 78 , 63 , 45 , 22 , 16 , 73 , 45 , 26 , 25 , 75 , 15 , 35 , 22 ,
105 , 1 , 105 , 73 , 21 , 89 , 5 , 66 , 48 , 78 , 89 , 38 , 15 , 25 , 97 ,
66 , 9 , 27 , 27 , 49 , 48 , 3 , 26 , 35 , 81 , 21 , 63 , 3 , 97 , 80 ,
38 , 81 , 16 , 1};
static unsigned int rem113[113]={
0 , 1 , 16 , 81 , 30 , 60 , 53 , 28 , 28 , 7 , 56 , 64 , 57 , 85 , 109 ,
1 , 109 , 14 , 112 , 32 , 105 , 8 , 7 , 53 , 8 , 97 , 4 , 2 , 49 , 14 ,
16 , 85 , 49 , 99 , 111 , 98 , 97 , 56 , 60 , 105 , 98 , 83 , 15 , 99 , 112 ,
81 , 57 , 2 , 15 , 106 , 83 , 4 , 64 , 30 , 32 , 111 , 106 , 106 , 111 , 32 ,
30 , 64 , 4 , 83 , 106 , 15 , 2 , 57 , 81 , 112 , 99 , 15 , 83 , 98 , 105 ,
60 , 56 , 97 , 98 , 111 , 99 , 49 , 85 , 16 , 14 , 49 , 2 , 4 , 97 , 8 ,
53 , 7 , 8 , 105 , 32 , 112 , 14 , 109 , 1 , 109 , 85 , 57 , 64 , 56 , 7 ,
28 , 28 , 53 , 60 , 30 , 81 , 16 , 1};
static unsigned int rem137[137]={
0 , 1 , 16 , 81 , 119 , 77 , 63 , 72 , 123 , 122 , 136 , 119 , 49 , 65 , 56 ,
72 , 50 , 88 , 34 , 34 , 121 , 78 , 123 , 87 , 99 , 38 , 81 , 18 , 74 , 87 ,
56 , 4 , 115 , 49 , 38 , 64 , 133 , 1 , 133 , 59 , 18 , 136 , 15 , 103 , 50 ,
78 , 22 , 15 , 77 , 115 , 60 , 4 , 63 , 103 , 14 , 121 , 88 , 14 , 22 , 122 ,
74 , 73 , 64 , 16 , 59 , 73 , 99 , 65 , 60 , 60 , 65 , 99 , 73 , 59 , 16 ,
64 , 73 , 74 , 122 , 22 , 14 , 88 , 121 , 14 , 103 , 63 , 4 , 60 , 115 , 77 ,
15 , 22 , 78 , 50 , 103 , 15 , 136 , 18 , 59 , 133 , 1 , 133 , 64 , 38 , 49 ,
115 , 4 , 56 , 87 , 74 , 18 , 81 , 38 , 99 , 87 , 123 , 78 , 121 , 34 , 34 ,
88 , 50 , 72 , 56 , 65 , 49 , 119 , 136 , 122 , 123 , 72 , 63 , 77 , 119 , 81 ,
16 , 1};

// up to 2*p-1 determine the biquadratric resideus, 1 means that it is a resideu, 0 means that is not a resideu

static unsigned int ispowerrem7[2*7]={
1 ,1 ,1 ,0 ,1 ,0 ,0 ,1 ,1 ,1 ,0 ,1 ,0 ,0};
static unsigned int ispowerrem13[2*13]={
1 ,1 ,0 ,1 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,0 ,0 ,1 ,1 ,
0 ,1 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,0 ,0};
static unsigned int ispowerrem17[2*17]={
1 ,1 ,0 ,0 ,1 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,
0 ,1 ,1 ,1 ,0 ,0 ,1 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,
1 ,0 ,0 ,1};
static unsigned int ispowerrem29[2*29]={
1 ,1 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,
0 ,1 ,0 ,0 ,0 ,1 ,0 ,0 ,1 ,1 ,1 ,0 ,0 ,0 ,1 ,
1 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,
1 ,0 ,0 ,0 ,1 ,0 ,0 ,1 ,1 ,1 ,0 ,0 ,0};
static unsigned int ispowerrem37[2*37]={
1 ,1 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,1 ,1 ,0 ,1 ,0 ,0 ,
0 ,1 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,0 ,0 ,
0 ,0 ,0 ,1 ,1 ,0 ,0 ,1 ,1 ,0 ,0 ,0 ,0 ,0 ,1 ,
0 ,1 ,1 ,0 ,1 ,0 ,0 ,0 ,1 ,0 ,0 ,0 ,0 ,0 ,0 ,
0 ,0 ,0 ,1 ,0 ,0 ,0 ,0 ,0 ,0 ,1 ,1 ,0 ,0};
static unsigned int ispowerrem41[2*41]={
1 ,1 ,0 ,0 ,1 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,0 ,0 ,0 ,
0 ,1 ,0 ,1 ,0 ,0 ,0 ,0 ,1 ,0 ,1 ,0 ,0 ,0 ,0 ,
0 ,1 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,0 ,1 ,1 ,1 ,0 ,0 ,
1 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,1 ,
0 ,0 ,0 ,0 ,1 ,0 ,1 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,0 ,
0 ,0 ,0 ,1 ,0 ,0 ,1};
static unsigned int ispowerrem53[2*53]={
1 ,1 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,0 ,1 ,0 ,
1 ,1 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,0 ,0 ,1 ,0 ,
0 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,1 ,
0 ,1 ,1 ,0 ,1 ,0 ,0 ,0 ,1 ,1 ,0 ,0 ,0 ,0 ,0 ,
0 ,0 ,0 ,1 ,0 ,0 ,1 ,0 ,1 ,1 ,0 ,0 ,0 ,0 ,0 ,
0 ,0 ,1 ,0 ,0 ,0 ,1 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,1 ,
0 ,0 ,0 ,0 ,0 ,1 ,0 ,1 ,0 ,1 ,1 ,0 ,1 ,0 ,0 ,
0};
static unsigned int ispowerrem61[2*61]={
1 ,1 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,0 ,1 ,1 ,0 ,
1 ,1 ,0 ,0 ,0 ,1 ,0 ,1 ,0 ,0 ,1 ,0 ,0 ,0 ,0 ,
0 ,0 ,0 ,0 ,1 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,0 ,
0 ,0 ,1 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,1 ,1 ,1 ,0 ,
0 ,1 ,1 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,0 ,1 ,1 ,
0 ,1 ,1 ,0 ,0 ,0 ,1 ,0 ,1 ,0 ,0 ,1 ,0 ,0 ,0 ,
0 ,0 ,0 ,0 ,0 ,1 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,
0 ,0 ,0 ,1 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,1 ,1 ,1 ,
0 ,0};
static unsigned int ispowerrem73[2*73]={
1 ,1 ,1 ,0 ,1 ,0 ,0 ,0 ,1 ,1 ,0 ,0 ,0 ,0 ,0 ,
0 ,1 ,0 ,1 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,
0 ,0 ,1 ,0 ,0 ,0 ,1 ,1 ,0 ,0 ,0 ,1 ,0 ,0 ,0 ,
0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,1 ,0 ,0 ,
0 ,0 ,0 ,0 ,1 ,1 ,0 ,0 ,0 ,1 ,0 ,1 ,1 ,1 ,1 ,
1 ,0 ,1 ,0 ,0 ,0 ,1 ,1 ,0 ,0 ,0 ,0 ,0 ,0 ,1 ,
0 ,1 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,
1 ,0 ,0 ,0 ,1 ,1 ,0 ,0 ,0 ,1 ,0 ,0 ,0 ,0 ,0 ,
0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,1 ,0 ,0 ,0 ,0 ,
0 ,0 ,1 ,1 ,0 ,0 ,0 ,1 ,0 ,1 ,1};
static unsigned int ispowerrem89[2*89]={
1 ,1 ,1 ,0 ,1 ,0 ,0 ,0 ,1 ,0 ,0 ,1 ,0 ,0 ,0 ,
0 ,1 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,0 ,1 ,0 ,0 ,0 ,0 ,
0 ,0 ,1 ,0 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,0 ,0 ,0 ,1 ,
1 ,0 ,0 ,0 ,0 ,1 ,0 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,0 ,
0 ,0 ,0 ,0 ,1 ,0 ,0 ,1 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,
0 ,0 ,0 ,1 ,0 ,0 ,1 ,0 ,0 ,0 ,1 ,0 ,1 ,1 ,1 ,
1 ,1 ,0 ,1 ,0 ,0 ,0 ,1 ,0 ,0 ,1 ,0 ,0 ,0 ,0 ,
1 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,0 ,1 ,0 ,0 ,0 ,0 ,0 ,
0 ,1 ,0 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,0 ,0 ,0 ,1 ,1 ,
0 ,0 ,0 ,0 ,1 ,0 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,0 ,0 ,
0 ,0 ,0 ,1 ,0 ,0 ,1 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,0 ,
0 ,0 ,1 ,0 ,0 ,1 ,0 ,0 ,0 ,1 ,0 ,1 ,1};
static unsigned int ispowerrem97[2*97]={
1 ,1 ,0 ,0 ,1 ,0 ,1 ,0 ,0 ,1 ,0 ,0 ,0 ,0 ,0 ,
0 ,1 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,1 ,0 ,0 ,0 ,0 ,0 ,
0 ,0 ,0 ,1 ,0 ,1 ,1 ,0 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,
0 ,0 ,1 ,0 ,0 ,1 ,0 ,0 ,0 ,1 ,0 ,0 ,0 ,0 ,0 ,
0 ,1 ,1 ,0 ,1 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,
1 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,
0 ,1 ,0 ,1 ,0 ,0 ,1 ,1 ,1 ,0 ,0 ,1 ,0 ,1 ,0 ,
0 ,1 ,0 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,0 ,0 ,0 ,0 ,1 ,
0 ,1 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,1 ,1 ,0 ,
0 ,0 ,0 ,0 ,0 ,1 ,0 ,0 ,0 ,1 ,0 ,0 ,1 ,0 ,0 ,
0 ,1 ,0 ,0 ,0 ,0 ,0 ,0 ,1 ,1 ,0 ,1 ,0 ,0 ,0 ,
0 ,0 ,0 ,0 ,0 ,1 ,0 ,1 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,
0 ,0 ,0 ,0 ,0 ,1 ,0 ,0 ,1 ,0 ,1 ,0 ,0 ,1};
static unsigned int ispowerrem101[2*101]={
1 ,1 ,0 ,0 ,0 ,1 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,
0 ,1 ,0 ,0 ,1 ,0 ,0 ,0 ,0 ,1 ,1 ,0 ,0 ,0 ,0 ,
0 ,1 ,0 ,0 ,0 ,0 ,1 ,1 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,
0 ,0 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,1 ,0 ,1 ,0 ,1 ,0 ,
0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,0 ,1 ,0 ,0 ,0 ,
0 ,0 ,0 ,1 ,1 ,1 ,1 ,0 ,0 ,1 ,0 ,0 ,1 ,1 ,0 ,
0 ,0 ,1 ,0 ,0 ,1 ,0 ,1 ,0 ,0 ,0 ,1 ,1 ,0 ,0 ,
0 ,1 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,0 ,
1 ,0 ,0 ,0 ,0 ,1 ,1 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,0 ,
0 ,0 ,1 ,1 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,
0 ,0 ,0 ,1 ,0 ,1 ,0 ,1 ,0 ,1 ,0 ,0 ,0 ,0 ,0 ,
0 ,0 ,0 ,0 ,1 ,0 ,0 ,1 ,0 ,0 ,0 ,0 ,0 ,0 ,1 ,
1 ,1 ,1 ,0 ,0 ,1 ,0 ,0 ,1 ,1 ,0 ,0 ,0 ,1 ,0 ,
0 ,1 ,0 ,1 ,0 ,0 ,0};
static unsigned int ispowerrem109[2*109]={
1 ,1 ,0 ,1 ,0 ,1 ,0 ,1 ,0 ,1 ,0 ,0 ,0 ,0 ,0 ,
1 ,1 ,0 ,0 ,0 ,0 ,1 ,1 ,0 ,0 ,1 ,1 ,1 ,0 ,0 ,
0 ,0 ,0 ,0 ,0 ,1 ,0 ,0 ,1 ,0 ,0 ,0 ,0 ,0 ,0 ,
1 ,0 ,0 ,1 ,1 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,
0 ,0 ,0 ,1 ,0 ,0 ,1 ,0 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,
1 ,0 ,0 ,1 ,0 ,1 ,1 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,1 ,
0 ,0 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,
1 ,0 ,0 ,0 ,1 ,1 ,0 ,1 ,0 ,1 ,0 ,1 ,0 ,1 ,0 ,
0 ,0 ,0 ,0 ,1 ,1 ,0 ,0 ,0 ,0 ,1 ,1 ,0 ,0 ,1 ,
1 ,1 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,0 ,1 ,0 ,0 ,
0 ,0 ,0 ,0 ,1 ,0 ,0 ,1 ,1 ,0 ,0 ,0 ,0 ,0 ,0 ,
0 ,0 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,0 ,1 ,0 ,0 ,0 ,0 ,
0 ,0 ,1 ,0 ,1 ,0 ,0 ,1 ,0 ,1 ,1 ,0 ,0 ,0 ,0 ,
0 ,0 ,0 ,1 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,0 ,0 ,
0 ,0 ,0 ,0 ,1 ,0 ,0 ,0};
static unsigned int ispowerrem113[2*113]={
1 ,1 ,1 ,0 ,1 ,0 ,0 ,1 ,1 ,0 ,0 ,0 ,0 ,0 ,1 ,
1 ,1 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,
1 ,0 ,1 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,
0 ,0 ,0 ,0 ,1 ,0 ,0 ,0 ,1 ,0 ,0 ,1 ,1 ,0 ,0 ,
1 ,0 ,0 ,0 ,1 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,
0 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,1 ,0 ,1 ,0 ,0 ,0 ,0 ,
0 ,0 ,0 ,0 ,0 ,0 ,0 ,1 ,1 ,1 ,0 ,0 ,0 ,0 ,0 ,
1 ,1 ,0 ,0 ,1 ,0 ,1 ,1 ,1 ,1 ,1 ,0 ,1 ,0 ,0 ,
1 ,1 ,0 ,0 ,0 ,0 ,0 ,1 ,1 ,1 ,0 ,0 ,0 ,0 ,0 ,
0 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,1 ,0 ,1 ,0 ,0 ,0 ,0 ,
0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,0 ,
0 ,1 ,0 ,0 ,1 ,1 ,0 ,0 ,1 ,0 ,0 ,0 ,1 ,0 ,0 ,
0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,1 ,
0 ,1 ,0 ,1 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,
1 ,1 ,1 ,0 ,0 ,0 ,0 ,0 ,1 ,1 ,0 ,0 ,1 ,0 ,1 ,
1};
static unsigned int ispowerrem137[2*137]={
1 ,1 ,0 ,0 ,1 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,1 ,
1 ,1 ,0 ,1 ,0 ,0 ,0 ,1 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,
0 ,0 ,0 ,0 ,1 ,0 ,0 ,0 ,1 ,0 ,0 ,0 ,0 ,0 ,0 ,
0 ,0 ,0 ,0 ,1 ,1 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,0 ,1 ,
1 ,0 ,0 ,1 ,1 ,1 ,0 ,0 ,0 ,0 ,0 ,0 ,1 ,1 ,1 ,
0 ,0 ,1 ,1 ,0 ,0 ,1 ,0 ,0 ,0 ,0 ,0 ,1 ,1 ,0 ,
0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,0 ,0 ,1 ,0 ,
0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,0 ,0 ,1 ,
0 ,1 ,1 ,1 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,
0 ,1 ,1 ,1 ,0 ,0 ,1 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,
0 ,1 ,1 ,1 ,0 ,1 ,0 ,0 ,0 ,1 ,0 ,0 ,0 ,0 ,0 ,
0 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,0 ,0 ,1 ,0 ,0 ,0 ,0 ,
0 ,0 ,0 ,0 ,0 ,0 ,1 ,1 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,
0 ,1 ,1 ,0 ,0 ,1 ,1 ,1 ,0 ,0 ,0 ,0 ,0 ,0 ,1 ,
1 ,1 ,0 ,0 ,1 ,1 ,0 ,0 ,1 ,0 ,0 ,0 ,0 ,0 ,1 ,
1 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,0 ,0 ,
1 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,1 ,0 ,0 ,
0 ,1 ,0 ,1 ,1 ,1 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,0 ,
1 ,0 ,0 ,1};

unsigned int X[15][137],sizes[2];
unsigned int R7,R13,R17,R29,R37,R41,R53,R61,R73,R89,R97,R101,R109,R113,R137;
unsigned int np=0,*smallprimes; // all odd primes up to sqrt(2*Range) that are not congurent by 1 mod 8
unsigned int A7[8],A13[14],A17[18],A29[30],A37[38],A41[42],A53[54],A61[62],A73[74],A89[90],A97[98],A101[102],A109[110],A113[114],A137[138];
static unsigned int modprimes[11]={7,13,17,29,37,41,53,61,73,89,97};
static unsigned int largeprimes[5]={1000000007,1000000009,1000000021,1000000033,1000000087};

static unsigned int good13rem[13]={1,1,1,1,1,1,1,0,0,1,1,0,1};
static unsigned int good29rem[29]={1,1,1,1,0,0,0,1,1,0,1,1,1,0,1,1,1,1,1,1,1,1,0,1,1,1,1,1,0};
unsigned int Inverserem[4][3125];
unsigned int *count17,*count29,*count481,*specialcount29,*specialcount481;
unsigned int **multipliers17,**multipliers29,**multipliers481,**specialmultipliers29,**specialmultipliers481;

static unsigned int factors[4]={1,5,3,2};
static unsigned int multiplier[4]={1,3125,243,256};
static unsigned int STEP[4]={1,3125,243,64};
static unsigned int num_cases[4]={1,4,2,2};
static unsigned int num_cases2[4]={1,2,2,2};
static unsigned int rem_mult_d[4][2];


void finalcheck(unsigned int a, unsigned int b, unsigned int c, unsigned int d)
{
    unsigned int i,p,u,GCD;

    for(i=0;i<5;i++)  {
        p=largeprimes[i];
        u=(powmod4(a,p)+p-powmod4(b,p)+p-powmod4(c,p)+p-powmod4(d,p))%p;
        if(u) return;
    }
//  print also (primitive) if it is a primitive solution so if gcd(a,b,c,d)=1 is true.
    printf("Solution found! %u^4=%u^4+%u^4+%u^4",a,b,c,d);
    GCD=gcd(a,gcd(b,gcd(c,d)));
    if(GCD==1)  printf("  (primitive)");
    printf("\n");
    out=fopen("results_euler(4,1,3).txt","a+");
    fprintf(out,"Solution found! %u^4=%u^4+%u^4+%u^4",a,b,c,d);
    if(GCD==1)  fprintf(out,"  (primitive)");
    fprintf(out,"\n");
    fclose(out);

    return;
}

void compute_d(unsigned int a, unsigned int b, unsigned int c)
{
// d^4=a^4-b^4-c^4 so it is easy to compute d using large numbers, but some powmod tricks we can avoid this.
// speed isn't interesting.
// It is good if Range<10^12
   unsigned int d,remp[2],remq[2],i,j,p,q,u;
   unsigned long long int D;

   p=1000039,q=1000151;// p==q==7 mod 8 primes
   static unsigned int inv_p_q=776903; // it is single_modinv(p,q)
   u=(powmod4(a,p)+p-powmod4(b,p)+p-powmod4(c,p))%p;
   remp[0]=powmod(u,(p+1)>>3,p);
   remp[1]=p-remp[0];
   u=(powmod4(a,q)+q-powmod4(b,q)+q-powmod4(c,q))%q;
   remq[0]=powmod(u,(q+1)>>3,q);
   remq[1]=q-remq[0];

   for(i=0;i<2;i++)  {
        for(j=0;j<2;j++)  {
            D=remp[i]+p*(((unsigned long long) (remq[j]+(q-remp[i])%q)*inv_p_q)%q);  
            if(D<a)  d=D,finalcheck(a,b,c,d);
        }
   }

   return;
}

void fastcheck(unsigned int a,unsigned int b)  // faster check for casenumber=2
{
   unsigned int rem3,rem1024,rem,remainder,f,g,h,i,i17,i29,i481,j,k,l,m,u,w,x,y,z,c1,c2,c3;
   unsigned long long int LA=a,LB=b;
   unsigned long long int A=LA*LA-LB*LB,B=LA*LA+LB*LB;

   R7=((A%7)*(B%7))%7;
   R41=((A%41)*(B%41))%41;
   R53=((A%53)*(B%53))%53;
   R61=((A%61)*(B%61))%61;
   R73=((A%73)*(B%73))%73;

   u=R7+7;
   for(i=0;i<4;i++)  w=ispowerrem7[u-rem7[i]],A7[i]=w,A7[7-i]=w;
   u=R41+41;
   for(i=0;i<21;i++)  w=ispowerrem41[u-rem41[i]],A41[i]=w,A41[41-i]=w;
   u=R53+53;
   for(i=0;i<27;i++)  w=ispowerrem53[u-rem53[i]],A53[i]=w,A53[53-i]=w;
   u=R61+61;
   for(i=0;i<31;i++)  w=ispowerrem61[u-rem61[i]],A61[i]=w,A61[61-i]=w;
   u=R73+73;
   for(i=0;i<37;i++)  w=ispowerrem73[u-rem73[i]],A73[i]=w,A73[73-i]=w;

   i17=17+powmod4(a,17)-powmod4(b,17);
   if(i17>=17)  i17-=17;
   i29=29+powmod4(a,29)-powmod4(b,29);
   if(i29>=29)  i29-=29;
   i481=481+powmod4(a,481)-powmod4(b,481);
   if(i481>=481)  i481-=481;

        unsigned long long int Lw=((A&65535)*(B&65535))&65535;
        rem1024=a&1023;
        remainder=powmod4(rem1024,65536);
        rem3=single_modinv(powmod(rem1024,3,16),16);
            w=(rem3*((Lw+65536-remainder+65536-4096)>>12))&15;
            for(g=0;g<2;g++)  {
                if(g)  rem=rem1024+(w<<10);
                else   rem=16384-rem1024-(w<<10);
                rem+=(rem%5)<<14;
                x=29*i29+rem%29;
                c1=count29[x];
                for(h=0;h<c1;h++)  {
                    k=rem+multipliers29[x][h]*81920;
                    y=17*i17+k%17;
                    c2=count17[y];
                    for(i=0;i<c2;i++)  {
                        l=k+multipliers17[y][i]*2375680;
                        z=481*i481+l%481;
                        c3=count481[z];
                        for(j=0;j<c3;j++)  {
                            m=l+multipliers481[z][j]*40386560;
                            if(m>=a)  break;
                            if(A73[m%73]&&A61[m%61]&&A53[m%53]&&A41[m%41]&&A7[m%7])  compute_d(a,b,m);
                        }
                    }
                }
            }

        Lw=((A&1048575)*(B&1048575))&1048575;
        rem1024=a&1023;
        remainder=powmod4(rem1024,1048576);
        rem3=single_modinv(powmod(rem1024,3,256),256);
        for(f=0;f<2;f++)  {
            w=(rem3*((Lw+1048576-remainder+1048576-(f<<16))>>12))&255;
            for(g=0;g<2;g++)  {
                if(g)  rem=rem1024+(w<<10);
                else   rem=262144-rem1024-(w<<10);
                rem+=(rem%5)<<18;
                x=29*i29+rem%29;
                c1=specialcount29[x];
                for(h=0;h<c1;h++)  {
                    k=rem+specialmultipliers29[x][h]*1310720;
                    z=481*i481+k%481;
                    c3=specialcount481[z];
                    for(j=0;j<c3;j++)  {
                         m=k+specialmultipliers481[z][j]*38010880;
                         if(m>=a)  break;
                         if(A73[m%73]&&A61[m%61]&&A53[m%53]&&A41[m%41]&&A7[m%7])  compute_d(a,b,m);
                    }
                }
            }
        }        
   return;
}

void check(unsigned int a, unsigned int b, unsigned int casenumber)
{
   if((good13rem[(13+powmod4(a,13)-powmod4(b,13))%13]==0)||(good29rem[(29+powmod4(a,29)-powmod4(b,29))%29]==0))  return;

   unsigned long long int LA=a,LB=b;
   unsigned long long int A=LA*LA-LB*LB;
   unsigned long long int B=LA*LA+LB*LB;
   unsigned int M,exponent,f,g,h,i,j,k,l,m,p,s,u,w,MBIG,num1,num2,num_L,num_R,num_temp;
   unsigned int M1,M2,MM,biginv,inv,inv2,rem1024,specialtwo;
   unsigned int bound,step,step2,smallstep,remainder,rem;
   unsigned int position,blockingtwo,largemod,S1,T1,T2,pow,limit;
   unsigned long long int Lw;

   position=0;
   specialtwo=0;

   // we know that A is divisible by 2048 and B is even if case=1, using this fact at the definition of M
   if(casenumber==1)  A>>=11,B>>=1,M=8,largemod=8;
   else         M=8192,specialtwo=0,largemod=16384;  //  we can't use specialtwo if case=2
   
   exponent=0;
   while((A&1)==0)  A>>=1,exponent++;
   while((B&1)==0)  B>>=1,exponent++;

   while(exponent>=4)  exponent-=4,M<<=1,largemod<<=1;

   if(exponent>1)  return;
   if(exponent==1) A<<=1;  // remultiple the factor of two
   if((((A&15)*(B&15))&15)>2)  return;

   exponent=0;
   while(A%5==0)  A=A/5,exponent++;
   while(B%5==0)  B=B/5,exponent++;
   if((exponent&3)!=0)  return;
   if(((A%5)*(B%5))%5>2)  return;
   while(exponent>0)  exponent-=4,M*=5,largemod*=5;

   if(casenumber==1)  limit=np;
   else               limit=168;
   
   if(limit>np)  limit=np;

   for(i=0;i<limit;i++)  {
       p=smallprimes[i];
       exponent=0;
       while(A%p==0)  A=A/p,exponent++;
       while(B%p==0)  B=B/p,exponent++;
       if((exponent&3)!=0)  return;
       while(exponent>0)  exponent-=4,M*=p,largemod*=p;
   }

   R13=((A%13)*(B%13))%13;
   R29=((A%29)*(B%29))%29;
   if((good13rem[R13]==0)||(good29rem[R29]==0))  return;

   if(casenumber==2)  fastcheck(a,b);
   else {

   if(casenumber==1)  {
       blockingtwo=0;
       if((((A%5)*(B%5))%5==1)&&(0x3fffffff/largemod>3125))  position=1,largemod*=3125;
       else if((((A%3)*(B%3))%3==1)&&(0x3fffffff/largemod>243))  position=2,largemod*=243;
       else if(((((A&15)*(B&15))&15)==1)&&(0x3fffffff/largemod>64))  blockingtwo=1,position=3,largemod<<=6;
   // if A*B==2 mod 16 then we know that c and d are odd numbers.
          if((blockingtwo==0)&&((((A&15)*(B&15))&15)==2)&&(0x3fffffff/largemod>2))  specialtwo=1,largemod<<=1;
   }

   R7=((A%7)*(B%7))%7;
   R17=((A%17)*(B%17))%17;
   R37=((A%37)*(B%37))%37;
   R41=((A%41)*(B%41))%41;
   R53=((A%53)*(B%53))%53;
   R61=((A%61)*(B%61))%61;
   R73=((A%73)*(B%73))%73;
   R89=((A%89)*(B%89))%89;
   R97=((A%97)*(B%97))%97;
   R101=((A%101)*(B%101))%101;
   R109=((A%109)*(B%109))%109;
   R113=((A%113)*(B%113))%113;
   R137=((A%137)*(B%137))%137;

   u=R7+7;
   for(i=0;i<4;i++)  w=ispowerrem7[u-rem7[i]],X[0][i]=w,X[0][7-i]=w,A7[i]=w,A7[7-i]=w;
   u=R13+13;
   for(i=0;i<7;i++)  w=ispowerrem13[u-rem13[i]],X[1][i]=w,X[1][13-i]=w,A13[i]=w,A13[13-i]=w;
   u=R17+17;
   for(i=0;i<9;i++)  w=ispowerrem17[u-rem17[i]],X[2][i]=w,X[2][17-i]=w,A17[i]=w,A17[17-i]=w;
   u=R29+29;
   for(i=0;i<15;i++)  w=ispowerrem29[u-rem29[i]],X[3][i]=w,X[3][29-i]=w,A29[i]=w,A29[29-i]=w;
   u=R37+37;
   for(i=0;i<19;i++)  w=ispowerrem37[u-rem37[i]],X[4][i]=w,X[4][37-i]=w,A37[i]=w,A37[37-i]=w;
   u=R41+41;
   for(i=0;i<21;i++)  w=ispowerrem41[u-rem41[i]],X[5][i]=w,X[5][41-i]=w,A41[i]=w,A41[41-i]=w;
   u=R53+53;
   for(i=0;i<27;i++)  w=ispowerrem53[u-rem53[i]],X[6][i]=w,X[6][53-i]=w,A53[i]=w,A53[53-i]=w;
   u=R61+61;
   for(i=0;i<31;i++)  w=ispowerrem61[u-rem61[i]],X[7][i]=w,X[7][61-i]=w,A61[i]=w,A61[61-i]=w;
   u=R73+73;
   for(i=0;i<37;i++)  w=ispowerrem73[u-rem73[i]],X[8][i]=w,X[8][73-i]=w,A73[i]=w,A73[73-i]=w;
   u=R89+89;
   for(i=0;i<45;i++)  w=ispowerrem89[u-rem89[i]],X[9][i]=w,X[9][89-i]=w,A89[i]=w,A89[89-i]=w;
   u=R97+97;
   for(i=0;i<49;i++)  w=ispowerrem97[u-rem97[i]],X[10][i]=w,X[10][97-i]=w,A97[i]=w,A97[97-i]=w;
   u=R101+101;
   for(i=0;i<51;i++)  w=ispowerrem101[u-rem101[i]],X[11][i]=w,X[11][101-i]=w,A101[i]=w,A101[101-i]=w;
   u=R109+109;
   for(i=0;i<55;i++)  w=ispowerrem109[u-rem109[i]],X[12][i]=w,X[12][109-i]=w,A109[i]=w,A109[109-i]=w;
   u=R113+113;
   for(i=0;i<57;i++)  w=ispowerrem113[u-rem113[i]],X[13][i]=w,X[13][113-i]=w,A113[i]=w,A113[113-i]=w;
   u=R137+137;
   for(i=0;i<69;i++)  w=ispowerrem137[u-rem137[i]],X[14][i]=w,X[14][137-i]=w,A137[i]=w,A137[137-i]=w;


   num1=0,M1=1,num2=0,M2=1;
   MM=1;// it is M1*M2

   unsigned int parity=0,pos=1,prm=modprimes[1];

   num_R=1,num_L=1;
   R[0]=0,L[0]=0,sizes[0]=1,sizes[1]=1;

   while((pos<11)&&((unsigned int) a/largemod/2>prm))  {
          if(((unsigned int) table_size/prm>sizes[parity])&&(((prm&7)==5)||(((A%prm)*(B%prm))%prm>0)))  {
          // use prm in the modulus
               if(parity==0)  {
                  num1++;
                  num_temp=num_L;
                  num_L=0;
                  inv=single_modinv(prm,M1);
                  for(i=0;i<num_temp;i++)  temp[i]=L[i];
                  for(i=0;i<prm;i++)  {
                      if(X[pos][i])  {
                         u=prm*M1-i;
                         for(j=0;j<num_temp;j++)  L[num_L]=i+prm*(((temp[j]+u)*inv)%M1),num_L++;
                      }
                  }
                  sizes[0]=num_L;
                  M1*=prm;
                  largemod*=prm;
               }
               else  {
                  num2++;
                  num_temp=num_R;
                  num_R=0;
                  inv=single_modinv(prm,M2);
                  for(i=0;i<num_temp;i++)  temp[i]=R[i];
                  for(i=0;i<prm;i++)  {
                      if(X[pos][i])  {
                         u=prm*M2-i;
                         for(j=0;j<num_temp;j++)  R[num_R]=i+prm*(((temp[j]+u)*inv)%M2),num_R++;
                      }
                  }
                  sizes[1]=num_R;
                  M2*=prm;
                  largemod*=prm;
               }
          MM*=prm;
          parity=1-parity;
          }
          pos++,prm=modprimes[pos];
   }

   if(a/largemod/2>7)  {
// use also 7 in the modulus
      if((M1>M2)&&((unsigned int) table_size/7>sizes[1]))  {
         num_temp=num_R;
         num_R=0;
         inv=single_modinv(M2,7);
         for(i=0;i<num_temp;i++)  temp[i]=R[i];
         for(i=0;i<num_temp;i++)  {
              w=temp[i];
              u=7*M2-(w%7);
              for(j=0;j<7;j++)  {
                 if(A7[j])   R[num_R]=w+M2*(((j+u)*inv)%7),num_R++;
              }
         }
         M2*=7;
         MM*=7;
         largemod*=7;
      }
      else if ((unsigned int) table_size/7>sizes[0])  {
         num_temp=num_L;
         num_L=0;
         inv=single_modinv(M1,7);
         for(i=0;i<num_temp;i++)  temp[i]=L[i];
         for(i=0;i<num_temp;i++)  {
              w=temp[i];
              u=7*M1-(w%7);
              for(j=0;j<7;j++)  {
                  if(A7[j])  L[num_L]=w+M1*(((j+u)*inv)%7),num_L++;
              }
         }
         M1*=7;
         MM*=7;
         largemod*=7;
      }
  }


  if(casenumber==1)  {
      bound=(unsigned int) a/M;
      pow=multiplier[position];
      prm=factors[position];
      smallstep=STEP[position];
      step=(1+specialtwo)*smallstep*MM;
      step2=step>>1;
      w=((A%pow)*(B%pow))%pow;
      
      inv=single_modinv(pow,M1);
      inv2=single_modinv(M1*pow,M2);
      S1=M1*smallstep;
      for(g=0;g<num_cases2[position];g++)  {
          rem=(w+pow-rem_mult_d[position][g])%pow;
          for(m=rem;m<rem+num_cases[position];m++)  {
              s=Inverserem[position][m];
              T1=M1-(s%M1);
              for(i=0;i<num_L;i++)  {
                   l=s+smallstep*(((L[i]+T1)*inv)%M1);
                   T2=M2-(l%M2);
                   for(j=0;j<num_R;j++)  {
                       h=l+S1*(((R[j]+T2)*inv2)%M2);
                       if(specialtwo&&((h&1)==0))  h+=step2;
                       for(k=h;k<=bound;k+=step)   {
                           if(A137[k%137]&&A113[k%113]&&A109[k%109]&&A101[k%101]&&A97[k%97]&&A89[k%89]&&A73[k%73]&&A61[k%61])  compute_d(a,b,k*M);
                       }
                   }
              }
          }
      }
   }
   else  {// this branch never happen
        Lw=((A&65535)*(B&65535))&65535;
        rem1024=((a&1023)*single_modinv(M>>13,1024))&1023;
        remainder=powmod4(rem1024,65536);
        bound=(unsigned int) a/(M>>13);
        step=MM<<14;
        MBIG=M1<<14;
        inv=single_modinv(M1,16384);
        biginv=single_modinv(MBIG,M2);
        for(f=0;f<2;f++)  {
            w=(single_modinv(powmod(rem1024,3,16),16)*((Lw+65536-remainder+65536-(f<<12))>>12))&15;
            for(g=0;g<2;g++)  {
                if(g)  rem=rem1024+(w<<10);
                else   rem=16384-rem1024-(w<<10);
                for(i=0;i<num_L;i++)  {
                    l=L[i]+M1*(((rem+16384-(L[i]&16383))*inv)&16383);
                    u=M2-(l%M2);
                    for(j=0;j<num_R;j++)  {
                        h=l+MBIG*(((R[j]+u)*biginv)%M2);
                        for(k=h;k<=bound;k+=step)  {
                            if(A137[k%137]&&A113[k%113]&&A109[k%109]&&A101[k%101]&&A97[k%97]&&A89[k%89]&&A73[k%73]&&A61[k%61])  compute_d(a,b,k*(M>>13));
                        }
                    }
                }
            }
        }
   }
   }

   return;
}


int main ()  {

   int test;

   unsigned int R_parameter,nexttype;
   unsigned int start_a0,end_a0,start_b0;  
   char typesearch[32],continuework[32],inputs[64];

   FILE* workfile;
   workfile=fopen("euler413work.txt","r");
   if(workfile==NULL)  {
      printf("I haven't found unfinished work!\n");
      test=1;
      while(test)  {
            test=0;
            printf("Please give R parameter, the Range will be R*10240000: ");
            scanf("%u",&R_parameter);
            if((R_parameter<=0)||(R_parameter>=195))  printf("Bad R parameter, it should be 0<R<195\n"),test=1;
      }
      Range=R_parameter*625*16384;
      test=1;
      while(test)  {
            test=0;
            printf("Do you want to start an exhaustive search in this Range or\n");
            printf("only to search for special solutions?\n");
            printf("( y=full search, n=special search ) ");
            scanf("%s",typesearch);
            if(typesearch[0]==121)       complete_search=1;
            else if(typesearch[0]==110) complete_search=0;
            else {
                  test=1;
                  printf("Wrong answer!\n");
            }
       }
       test=1;
       while(test)  {
             test=0;
             printf("Give the start value of a0. It should be 0<=start_a0<=16384: ");
             scanf("%d",&start_a0);
             if(start_a0>16384)  printf("Wrong answer! 0<=start_a0<=16384\n"),test=1;
       }
       test=1;
       while(test)  {
             test=0;
             printf("Give the end value of a0. It should be start_a0<=end_a0<=16384: ");
             scanf("%d",&end_a0);
             if((end_a0<start_a0)||(end_a0>16384))  printf("Wrong answer! start_a0<=end_a0<=16384\n"),test=1;
       }
       start_b0=0;  // in all cases we run from start_b0=0      
       nexttype=0;  // in all cases we run from type=0
    }
    else {
         // printf("I've found the work file!\n");
         // printf("Do you want to continue the unfinished work? ( y/n ) ");
         // scanf("%s",&continuework);
         continuework[0]='y';  // new line
         if(continuework[0]=='y')  {
            printf("The program started to continue the unfinished work!\n");
            fgets(inputs,sizeof(inputs),workfile);
            fgets(inputs,sizeof(inputs),workfile);  
            if (!memcmp(inputs,"R_parameter=",12))  R_parameter=atol(&inputs[12]);
            else  {
                   printf("The workfile is corrupt!\n");
                   printf("I've removed the workfile!\n");
                   printf("Rerun the program. Exit.\n");
                   fclose(workfile);
                   remove("euler413work.txt");
                   exit(1);
            }
            fgets(inputs,sizeof(inputs),workfile);
            if (!memcmp(inputs,"typesearch=",11))   complete_search=atol(&inputs[11]);
            else  {
                   printf("The workfile is corrupt!\n");
                   printf("I've removed the workfile!\n");
                   printf("Rerun the program. Exit.\n");
                   fclose(workfile);
                   remove("euler413work.txt");
                   exit(1);
            }
            fgets(inputs,sizeof(inputs),workfile);
            if (!memcmp(inputs,"start_a0=",9))   start_a0=atol(&inputs[9]);
            else  {
                   printf("The workfile is corrupt!\n");
                   printf("I've removed the workfile!\n");
                   printf("Rerun the program. Exit.\n");
                   fclose(workfile);
                   remove("euler413work.txt");
                   exit(1);
            }
            fgets(inputs,sizeof(inputs),workfile);
            if (!memcmp(inputs,"nexttype=",9))   nexttype=atol(&inputs[9]);
            else  {
                   printf("The workfile is corrupt!\n");
                   printf("I've removed the workfile!\n");
                   printf("Rerun the program. Exit.\n");
                   fclose(workfile);
                   remove("euler413work.txt");
                   exit(1);
            }
            fgets(inputs,sizeof(inputs),workfile);
            if (!memcmp(inputs,"end_a0=",7))  end_a0=atol(&inputs[7]);
            else  {
                   printf("The workfile is corrupt!\n");
                   printf("I've removed the workfile!\n");
                   printf("Rerun the program. Exit.\n");
                   fclose(workfile);
                   remove("euler413work.txt");
                   exit(1);
            }
            fgets(inputs,sizeof(inputs),workfile);
            if (!memcmp(inputs,"start_b0=",9))  start_b0=atol(&inputs[9]);
            else  {
                   printf("The workfile is corrupt!\n");
                   printf("I've removed the workfile!\n");
                   printf("Rerun the program. Exit.\n");
                   fclose(workfile);
                   remove("euler413work.txt");
                   exit(1);
            }
           if((R_parameter<=0)||(R_parameter>=195))  {
               printf("In the workfile: bad R parameter, it should be 0<R<195\n");
               printf("I've removed the workfile!\n");            
               printf("Rerun the program. Exit.\n");
               fclose(workfile);
               remove("euler413work.txt");
               exit(1);
            }
            if(complete_search>1)  {
               printf("In the workfile: bad typesearch, it should be 1 for fullsearch and 0 for special search!\n");
               printf("I've removed the workfile!\n");            
               printf("Rerun the program. Exit.\n");
               fclose(workfile);
               remove("euler413work.txt");
               exit(1);
            }
            if(start_a0>16384)  {
               printf("In the workfile: bad start_a0, it should be 0<=start_a0<=16384\n");
               printf("I've removed the workfile!\n");            
               printf("Rerun the program. Exit.\n");
               fclose(workfile);
               remove("euler413work.txt");
               exit(1);
            }
            if(nexttype>1)  {
               printf("In the workfile: bad nexttype, it should be 0 or 1 ( giving the next unfinished type for start_a0\n");
               printf("I've removed the workfile!\n");            
               printf("Rerun the program. Exit.\n");
               fclose(workfile);
               remove("euler413work.txt");
               exit(1);
            }
            if((end_a0<start_a0)||(end_a0>16384))  {
               printf("In the workfile: bad end_a0, it should be start_a0<=end_a0<=16384\n");
               printf("I've removed the workfile!\n");            
               printf("Rerun the program. Exit.\n");
               fclose(workfile);
               remove("euler413work.txt");
               exit(1);
            }
            if(start_b0>16384)  {
               printf("In the workfile: bad start_b0, it should be start_b0<16384\n");
               printf("I've removed the workfile!\n");            
               printf("Rerun the program. Exit.\n");
               fclose(workfile);
               remove("euler413work.txt");
               exit(1);
            }
         }
         else {
               printf("So you don't want to continue the unfinished work.\n");
               printf("I've removed the workfile!\n");            
               printf("Rerun the program. Exit.\n");
               fclose(workfile);
               remove("euler413work.txt");
               exit(1);
            }
         printf("Continue the computation at a0=%u,type=%u,b0=%u for R=%u\n",start_a0,nexttype,start_b0,R_parameter);
         Range=R_parameter*625*16384;
         fclose(workfile);
   }

   R=(unsigned int*)  malloc(table_size*sizeof(unsigned int));
   L=(unsigned int*)  malloc(table_size*sizeof(unsigned int));
   temp=(unsigned int*)  malloc(table_size*sizeof(unsigned int));

   unsigned int rem625[625];
   unsigned int rem3125[3125];
   unsigned int Inverserem625[625];
   unsigned int *Table;
   unsigned int inv_16384_625;

   unsigned int a,b,f,g,h,i,j,k,m,pos,s,step,u,limit,diff;
   unsigned int a0,a1,b0,b1,T,expo,blocksize,st,rem120,E,G,allsec;
   unsigned int *isprime;
   unsigned int A[10];
   unsigned int convert120[120]={0,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,
1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,
2,2,2,2,2,2,2,2,2,2,3,3,3,3,3,3,
3,3,4,4,4,4,4,4,4,4,4,4,4,4,4,4,
4,4,4,4,4,4,4,4,4,4,5,5,5,5,5,5,
5,5,5,5,5,5,5,5,5,5,6,6,6,6,6,6,
6,6,7,7,7,7,7,7,7,7,7,7,7,7,7,7,
7,7,8,8,8,8,8,8};  // used to convert the Table


// PARI code to generate convert120:
// s=0;for(n=0,119,print1(s",");if(n%16==15,print1("\n"));if((n%8==1)&&(gcd(n,15)==1),s++))

   double DD;

   printf("Building up some tables\n");

   A[0]=1,A[1]=1,A[2]=1,A[3]=0,A[4]=0;
   A[5]=1,A[6]=1,A[7]=1,A[8]=0,A[9]=0;

   rem_mult_d[0][0]=0,rem_mult_d[1][0]=0,rem_mult_d[2][0]=0,rem_mult_d[3][0]=0;
   rem_mult_d[0][1]=0,rem_mult_d[1][1]=625,rem_mult_d[2][1]=81,rem_mult_d[3][1]=16;

   Table=(unsigned int*) (malloc) ((Range/240+2)*sizeof(unsigned int));
   
   // Check if there was enough memory or not.
   if(Table==NULL)  {
      printf("Not enough memory on this computer, sorry.\nExit.\n");
      exit(1);
   }

   for(i=0;i<625;i++)  Inverserem625[i]=0;
   for(i=0;i<625;i++)  {
       u=powmod4(i,625);
       rem625[i]=u;
       if(u!=0)  {
          pos=Inverserem625[u-1];
          Inverserem625[u+pos]=i,Inverserem625[u-1]++;
       }
   }

   for(i=0;i<3125;i++)  rem3125[i]=powmod4(i,3125);

   for(i=0;i<=3;i++)  {
        for(j=0;j<3125;j++)  Inverserem[i][j]=0;
   }
   for(i=1;i<=3;i++)  {
       s=multiplier[i];
       k=factors[i];
       for(j=0;j<STEP[i];j++)  {
           u=powmod4(j,s);
           if(j%k>0)  pos=Inverserem[i][u-1],Inverserem[i][u+pos]=j,Inverserem[i][u-1]++;
       }
   }

   DD=(double) sqrt((double) 2.0*Range);
   E=2+(unsigned int) DD;
   isprime=(unsigned int*) (malloc) (E*sizeof(unsigned int));
   
   G=Range/240+1;
   for(i=0;i<=G;i++)  Table[i]=0xffffffff;
   
   for(i=0;i<E;i++)  isprime[i]=1;
   isprime[0]=0,isprime[1]=0;
   for(i=2;i*i<E;i++)  {
       if(isprime[i])  {
          for(j=i*i;j<E;j+=i)  isprime[j]=0;
       }
   }   

   for(i=7;i<E;i+=2)  {
       if(isprime[i]&&(i%8>1))  {
          for(j=0;j<120;j++)  {
              st=i*j;
              if((st%8==1)&&(st%3>0)&&(st%5>0))  {
                  blocksize=120*i;
                  for(k=st;k<=2*Range;k+=blocksize)  {
                      expo=0;
                      h=k;
                      while(h%i==0)  h/=i,expo++;
                      if((expo&3)>0)  {                    
                          rem120=((k/120)<<3)+convert120[k%120];
                          Table[rem120>>5]&=~Bits[rem120&31];
                      }
                  }
              }
          }
       }
   }

   for(i=3;i<100;i+=2)
       if(isprime[i]&&(i%8>1))  np++;
   
   for(i=101;i<E;i+=8)
       if(isprime[i])  np++;   
   
   smallprimes=(unsigned int*) (malloc) (np*sizeof(unsigned int));
   np=0;
   for(i=3;i<100;i+=2)
       if(isprime[i]&&(i%8>1))  smallprimes[np]=i,np++;
   
   for(i=101;i<E;i+=8)
       if(isprime[i])  smallprimes[np]=i,np++;

   unsigned int stored[512];
   unsigned int count;
   multipliers17=(unsigned int**) (malloc) (17*17*sizeof(unsigned int));
   multipliers29=(unsigned int**) (malloc) (29*29*sizeof(unsigned int));
   multipliers481=(unsigned int**) (malloc) (481*481*sizeof(unsigned int));
   specialmultipliers29=(unsigned int**) (malloc) (29*29*sizeof(unsigned int));
   specialmultipliers481=(unsigned int**) (malloc) (481*481*sizeof(unsigned int));
   count17=(unsigned int*) (malloc) (17*17*sizeof(int));
   count29=(unsigned int*) (malloc) (29*29*sizeof(int));
   count481=(unsigned int*) (malloc) (481*481*sizeof(int));
   specialcount29=(unsigned int*) (malloc) (29*29*sizeof(int));
   specialcount481=(unsigned int*) (malloc) (481*481*sizeof(int));

   for(i=0;i<17;i++)  {
       for(j=0;j<17;j++)  {
           count=0;
           for(k=0;k<17;k++)  {
               if(ispowerrem17[(i+17-rem17[(j+k*2375680)%17])%17])  stored[count]=k,count++;
           }
           h=17*i+j;
           count17[h]=count;
           multipliers17[h]=(unsigned int*) (malloc) (count*sizeof(unsigned int));
           for(k=0;k<count;k++)  multipliers17[h][k]=stored[k]; 
       }
   }

   for(i=0;i<29;i++)  {
       for(j=0;j<29;j++)  {
           count=0;
           for(k=0;k<29;k++)  {
               if(ispowerrem29[(i+29-rem29[(j+k*81920)%29])%29])  stored[count]=k,count++;
           }
           h=29*i+j;
           count29[h]=count;
           multipliers29[h]=(unsigned int*) (malloc) (count*sizeof(unsigned int));
           for(k=0;k<count;k++)  multipliers29[h][k]=stored[k]; 
       }
   }

   for(i=0;i<481;i++)  {  // 13*37=481
       for(j=0;j<481;j++)  {
           count=0;
           for(k=0;k<50;k++)  {  // (unsigned int) 194*16384*625/5/17/29/16384=49
               if(ispowerrem13[(i+13-rem13[(j+k*40386560)%13])%13]&&ispowerrem37[(i+37-rem37[(j+k*40386560)%37])%37])  stored[count]=k,count++;
           }
           h=481*i+j;
           count481[h]=count;
           multipliers481[h]=(unsigned int*) (malloc) (count*sizeof(unsigned int));
           for(k=0;k<count;k++)  multipliers481[h][k]=stored[k]; 
       }
   }

   for(i=0;i<29;i++)  {
       for(j=0;j<29;j++)  {
           count=0;
           for(k=0;k<29;k++)  {
               if(ispowerrem29[(i+29-rem29[(j+k*1310720)%29])%29])  stored[count]=k,count++;
          }
           h=29*i+j;
           specialcount29[h]=count;
           specialmultipliers29[h]=(unsigned int*) (malloc) (count*sizeof(unsigned int));
           for(k=0;k<count;k++)  specialmultipliers29[h][k]=stored[k]; 
       }
   }

   for(i=0;i<481;i++)  {  // 13*37=481
       for(j=0;j<481;j++)  {
           count=0;
           for(k=0;k<53;k++)  {  // (unsigned int) 194*16384*625/5/29/262144=52
               if(ispowerrem13[(i+13-rem13[(j+k*38010880)%13])%13]&&ispowerrem37[(i+37-rem37[(j+k*38010880)%37])%37])  stored[count]=k,count++;
           }
           h=481*i+j;
           specialcount481[h]=count;
           specialmultipliers481[h]=(unsigned int*) (malloc) (count*sizeof(unsigned int));
           for(k=0;k<count;k++)  specialmultipliers481[h][k]=stored[k]; 
       }
   }

   step=625*16384;
   inv_16384_625=14;// it is modinv(16384,625)

   printf("Done\n");

   // modify the original start_a0 and end_a0 values
   // Note that for the new values start_a0==end_a0==1 mod 8
   
   start_a0=(((start_a0+6)>>3)<<3)+1;
   end_a0=(((end_a0-1)>>3)<<3)+1;

   // modify the original start_b0 value
   unsigned int r1=start_a0&1023,r2=start_b0&1023;
   
   if(nexttype==0)  {
      if((r1!=r2)&&((r1+r2)!=1024)) {
           if(r1>r2)  start_b0+=r1-r2;
           else       start_b0+=2048-r1-r2;
      }
   }
   else {
      start_b0=((start_b0+7)>>3)<<3;
   }

// start the time after the tables build up
   time_t seconds=time(NULL);
   time_t previous_update=seconds;
   time_t date;

   for(a0=start_a0;a0<=end_a0;a0+=8)  {  // Note that a0==1 mod 8 should be to find primitive solutions.
   printf("Testing: a0=%u\n",a0);
   if((start_a0<a0)||(nexttype==0))  {
        for(b0=start_b0;b0<16384;)  {
           if(time(NULL)-previous_update>TIME_INTERVAL)  {
              previous_update=time(NULL);
              remove("euler413work.txt");
              workfile=fopen("euler413work.txt","a+");
              fprintf(workfile,"// Please don't modify this file\n");
              fprintf(workfile,"R_parameter=%u\n",R_parameter);
              fprintf(workfile,"typesearch=%u\n",complete_search);
              fprintf(workfile,"start_a0=%u\n",a0);
              fprintf(workfile,"nexttype=0\n");
              fprintf(workfile,"end_a0=%u\n",end_a0);
              fprintf(workfile,"start_b0=%u\n",b0);
              fclose(workfile);              
            }
                u=((powmod4(a0,65536)+65536-powmod4(b0,65536))&65535)>>12;
                if(u<=2)  {
                   for(h=1;h<5;h++)  {
                       for(g=h;g<625;g+=5)  {
                           u=g+625-(a0%625);
                           a1=a0+(((u*inv_16384_625)%625)<<14);
                           T=rem625[g];
                           for(f=T;f<T+4;f++)  {
                               u=Inverserem625[f]+625-(b0%625);
                               b1=b0+(((u*inv_16384_625)%625)<<14);
                               limit=(a1+step-b1)%step;
                               if(limit==0)  limit=step;
                               for(diff=limit;diff<Range;diff+=step)  {
                               //for(a=a1;a<Range;a+=step)  {
                               //    for(b=b1;b<a;b+=step)  {
                               // a-b=diff, note that diff>0
                                       k=diff;
                                       expo=0;
                                       while(k%3==0)  k/=3,expo++;
                                       if((expo&3)==0)  {
                                       while(k%5==0)  k/=5,expo++;
                                       if((expo&3)==0)  {  // not need to set expo=0, because we know that expo%4=0
                                       while((k&1)==0)  k>>=1;
                                       if((k&7)==1)  {
                                       rem120=((k/120)<<3)+convert120[k%120];
                                       if(Bits[rem120&31]&Table[rem120>>5])  {
                                       for(b=b1;b+diff<Range;b+=step)  {
                                       a=b+diff;
                                       m=a+b;
                                       expo=0;
                                       while(m%3==0)  m/=3,expo++;
                                       if((expo&3)==0)  {
                                       while(m%5==0)  m/=5,expo++;
                                       if((expo&3)==0)  {
                                       while((m&1)==0)  m>>=1;
                                       if((m&7)==1)  {
                                       rem120=((m/120)<<3)+convert120[m%120];
                                       if((Bits[rem120&31]&Table[rem120>>5])&&A[(3125+rem3125[a%3125]-rem3125[b%3125])/625])
                                           check(a,b,1);
                                       }}}}}}}
                                   }
                               }
                           }
                       }
                   }
                }
            if((b0&1023)<512)  b0+=1024-2*(b0&1023);
            else               b0+=2048-2*(b0&1023);
            }
            if(complete_search)  start_b0=0;
            else {
                  start_b0=(a0+8)&1023;
                  if(start_b0>512)  start_b0=1024-start_b0;
            }

        time(&date);
        allsec=time(NULL)-seconds;
  out=fopen("stat_euler(4,3,1).txt","a+");
  fprintf(out,"Finished: a0=%u,Range=%u,type=0,Time: %uh%um%us,Date: %s",a0,Range,allsec/3600,(allsec%3600)/60,allsec%60,ctime(&date));
  fclose(out);
        remove("euler413work.txt");
        workfile=fopen("euler413work.txt","a+");
        fprintf(workfile,"// Please don't modify this file\n");
        fprintf(workfile,"R_parameter=%u\n",R_parameter);
        fprintf(workfile,"typesearch=%u\n",complete_search);
        fprintf(workfile,"start_a0=%u\n",a0+8-8*complete_search);
        fprintf(workfile,"nexttype=%u\n",complete_search);
        fprintf(workfile,"end_a0=%u\n",end_a0);
        fprintf(workfile,"start_b0=%u\n",start_b0);
        fclose(workfile);
        printf("Finished: a0=%u,Range=%u,type=0,Time: %uh%um%us,Date: %s",a0,Range,allsec/3600,(allsec%3600)/60,allsec%60,ctime(&date));
       }

        if(complete_search)  {

           for(b0=start_b0;b0<16384;b0+=8)  {
           if(time(NULL)-previous_update>TIME_INTERVAL)  {
              previous_update=time(NULL);
              remove("euler413work.txt");
              workfile=fopen("euler413work.txt","a+");
              fprintf(workfile,"// Please don't modify this file\n");
              fprintf(workfile,"R_parameter=%u\n",R_parameter);
              fprintf(workfile,"typesearch=%u\n",complete_search);
              fprintf(workfile,"start_a0=%u\n",a0);
              fprintf(workfile,"nexttype=1\n");
              fprintf(workfile,"end_a0=%u\n",end_a0);
              fprintf(workfile,"start_b0=%u\n",b0);
              fclose(workfile);
            }
               for(h=1;h<5;h++)  {
                   for(g=h;g<625;g+=5)  {
                       u=g+625-(a0%625);
                       a1=a0+(((u*inv_16384_625)%625)<<14);
                       T=rem625[g];
                       for(f=T;f<T+4;f++)  {
                           u=Inverserem625[f]+625-(b0%625);
                           b1=b0+(((u*inv_16384_625)%625)<<14);
                               limit=(a1+step-b1)%step;
                               if(limit==0)  limit=step;
                               for(diff=limit;diff<Range;diff+=step)  {
                           //for(a=a1;a<Range;a+=step)  {
                           //    for(b=b1;b<a;b+=step)  {
                           //            k=a-b;
                                       k=diff;
                                       expo=0;
                                       while(k%3==0)  k/=3,expo++;
                                       if((expo&3)==0)  {
                                       while(k%5==0)  k/=5,expo++;
                                       if((expo&3)==0)  {
                                       while((k&1)==0)  k>>=1;
                                       if((k&7)==1)  {
                                       rem120=((k/120)<<3)+convert120[k%120];
                                       if(Bits[rem120&31]&Table[rem120>>5])  {
                                       for(b=b1;b+diff<Range;b+=step)  {
                                       a=b+diff;
                                       m=a+b;
                                       expo=0;
                                       while(m%3==0)  m/=3,expo++;
                                       if((expo&3)==0)  {
                                       while(m%5==0)  m/=5,expo++;
                                       if((expo&3)==0)  {
                                       while((m&1)==0)  m>>=1;
                                       if((m&7)==1)  {
                                       rem120=((m/120)<<3)+convert120[m%120];
                                       if((Bits[rem120&31]&Table[rem120>>5])&&A[(3125+rem3125[a%3125]-rem3125[b%3125])/625])
                                           check(a,b,2);
                                       }}}}}}}
                               }
                           }
                       }
                   }
               }
           }
        time(&date);
        allsec=time(NULL)-seconds;
        out=fopen("stat_euler(4,3,1).txt","a+");
        fprintf(out,"Finished: a0=%u,Range=%u,type=1,Time: %uh%um%us,Date: %s",a0,Range,allsec/3600,(allsec%3600)/60,allsec%60,ctime(&date));
        fclose(out);
        remove("euler413work.txt");
        workfile=fopen("euler413work.txt","a+");
        fprintf(workfile,"// Please don't modify this file\n");
        fprintf(workfile,"R_parameter=%u\n",R_parameter);
        fprintf(workfile,"typesearch=%u\n",complete_search);
        fprintf(workfile,"start_a0=%u\n",a0+8);
        fprintf(workfile,"nexttype=0\n");
        fprintf(workfile,"end_a0=%u\n",end_a0);
        start_b0=(a0+8)&1023;
        if(start_b0>512)  start_b0=1024-start_b0;
        fprintf(workfile,"start_b0=%u\n",start_b0);
        fclose(workfile);

        printf("Finished: a0=%u,Range=%u,type=1,Time: %uh%um%us,Date: %s",a0,Range,allsec/3600,(allsec%3600)/60,allsec%60,ctime(&date));
        }
  }

  remove("euler413work.txt");

  time(&date);
  allsec=time(NULL)-seconds;
  printf("Time: %uh%um%us,Date: %s",allsec/3600,(allsec%3600)/60,allsec%60,ctime(&date));

  free(isprime);
  free(Table);
  free(L);
  free(R);
  free(temp);
  free(count17);
  free(count29);
  free(count481);
  free(specialcount29);
  free(specialcount481);
  for(i=0;i<289;i++)  free(multipliers17[i]);
  free(multipliers17);
  for(i=0;i<841;i++)  free(multipliers29[i]);
  free(multipliers29);
  for(i=0;i<231361;i++) free(multipliers481[i]);
  free(multipliers481);
  for(i=0;i<841;i++)  free(specialmultipliers29[i]);
  free(specialmultipliers29);
  for(i=0;i<231361;i++) free(specialmultipliers481[i]);
  free(specialmultipliers481);

  return 0;
}
