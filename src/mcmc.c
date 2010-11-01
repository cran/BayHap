   #include <stdlib.h>
   #include <math.h>
   #include <stdio.h>
   #include <string.h> 
   #include <time.h>     
   #define norm  2.328306549295727688e-10
   #define m1    4294967087.0
   #define m2    4294944443.0
   #define a12     1403580.0
   #define a13n     810728.0
   #define a21      527612.0
   #define a23n    1370589.0
   #define two17   131072.0
   #define two53   9007199254740992.0
   #define fact  5.9604644775390625e-8       
   #define PI 3.141593



    typedef struct{
             int **val;
    }matriu_int;  
    typedef struct{
            double **val2;
    }matriu_doub;      
    typedef struct {
            int *mat;
            int imax,jmax;
    }matriu_vec;
    typedef struct{ 
            int *v;
            double llargada;
    }vec_int;
    typedef struct{
            double *v;
            int llargada;
    }vec_doub;
    typedef struct{ 
            double val2[2]; 
    }vdos;

     struct RngStream_InfoState {
           double Cg[6], Bg[6], Ig[6];
           int Anti;
           int IncPrec;
           char *name;
    };

    typedef struct RngStream_InfoState * RngStream;




static double nextSeed[6] = { 12345, 12345, 12345, 12345, 12345, 12345 };


/* The following are the transition matrices of the two MRG components */
/* (in matrix form), raised to the powers -1, 1, 2^76, and 2^127, resp.*/
static double InvA1[3][3] = {          /* Inverse of A1p0 */
          { 184888585.0,   0.0,  1945170933.0 },
          {         1.0,   0.0,           0.0 },
          {         0.0,   1.0,           0.0 }
          };

static double InvA2[3][3] = {          /* Inverse of A2p0 */
          {      0.0,  360363334.0,  4225571728.0 },
          {      1.0,          0.0,           0.0 },
          {      0.0,          1.0,           0.0 }
          };

static double A1p0[3][3] = {
          {       0.0,        1.0,       0.0 },
          {       0.0,        0.0,       1.0 },
          { -810728.0,  1403580.0,       0.0 }
          };

static double A2p0[3][3] = {
          {        0.0,        1.0,       0.0 },
          {        0.0,        0.0,       1.0 },
          { -1370589.0,        0.0,  527612.0 }
          };

static double A1p76[3][3] = {
          {      82758667.0, 1871391091.0, 4127413238.0 }, 
          {    3672831523.0,   69195019.0, 1871391091.0 }, 
          {    3672091415.0, 3528743235.0,   69195019.0 }
          };

static double A2p76[3][3] = {
          {    1511326704.0, 3759209742.0, 1610795712.0 }, 
          {    4292754251.0, 1511326704.0, 3889917532.0 }, 
          {    3859662829.0, 4292754251.0, 3708466080.0 }
          };

static double A1p127[3][3] = {
          {    2427906178.0, 3580155704.0,  949770784.0 }, 
          {     226153695.0, 1230515664.0, 3580155704.0 },
          {    1988835001.0,  986791581.0, 1230515664.0 }
          };

static double A2p127[3][3] = {
          {    1464411153.0,  277697599.0, 1610723613.0 },
          {      32183930.0, 1464411153.0, 1022607788.0 },
          {    2824425944.0,   32183930.0, 2093834863.0 }
          };





/*-------------------------------------------------------------------------*/

static double MultModMmcmc (double a, double s, double c, double m)
   /* Compute (a*s + c) % m. m must be < 2^35.  Works also for s, c < 0 */
{
   double v;
   long a1;
   v = a * s + c;
   if ((v >= two53) || (v <= -two53)) {
      a1 = (long) (a / two17);
      a -= a1 * two17;
      v = a1 * s;
      a1 = (long) (v / m);
      v -= a1 * m;
      v = v * two17 + a * s + c;
   }
   a1 = (long) (v / m);
   if ((v -= a1 * m) < 0.0)
      return v += m;
   else
      return v;
}


/*-------------------------------------------------------------------------*/

static void MatVecModMmcmc (double A[3][3], double s[3], double v[3], double m)
   /* Returns v = A*s % m.  Assumes that -m < s[i] < m. */
   /* Works even if v = s. */
{
   int i;
   double x[3];
   for (i = 0; i < 3; ++i) {
      x[i] = MultModMmcmc(A[i][0], s[0], 0.0, m);
      x[i] = MultModMmcmc (A[i][1], s[1], x[i], m);
      x[i] = MultModMmcmc (A[i][2], s[2], x[i], m);
   }
   for (i = 0; i < 3; ++i)
      v[i] = x[i];
}



/*-------------------------------------------------------------------------*/

static void MatMatModMmcmc (double A[3][3], double B[3][3], double C[3][3],
                        double m)
   /* Returns C = A*B % m. Work even if A = C or B = C or A = B = C. */
{
   int i, j;
   double V[3], W[3][3];
   for (i = 0; i < 3; ++i) {
      for (j = 0; j < 3; ++j)
         V[j] = B[j][i];
      MatVecModMmcmc(A, V, V, m);
      for (j = 0; j < 3; ++j)
         W[j][i] = V[j];
   }
   for (i = 0; i < 3; ++i) {
      for (j = 0; j < 3; ++j)
         C[i][j] = W[i][j];
   }
}



/*-------------------------------------------------------------------------*/

static void MatTwoPowModMmcmc (double A[3][3], double B[3][3], double m, long e)
  /* Compute matrix B = (A^(2^e) % m);  works even if A = B */
{
   int i, j;

   /* initialize: B = A */
   if (A != B) {
      for (i = 0; i < 3; i++) {
         for (j = 0; j < 3; ++j)
            B[i][j] = A[i][j];
      }
   }
   /* Compute B = A^{2^e} */
   for (i = 0; i < e; i++)
      MatMatModMmcmc (B, B, B, m);
}



/*-------------------------------------------------------------------------*/

static void MatPowModMmcmc (double A[3][3], double B[3][3], double m, long n)
   /* Compute matrix B = A^n % m ;  works even if A = B */
{
   int i, j;
   double W[3][3];

   /* initialize: W = A; B = I */
   for (i = 0; i < 3; i++) {
      for (j = 0; j < 3; ++j) {
         W[i][j] = A[i][j];
         B[i][j] = 0.0;
      }
   }
   for (j = 0; j < 3; ++j)
      B[j][j] = 1.0;

   /* Compute B = A^n % m using the binary decomposition of n */
   while (n > 0) {
      if (n % 2)
         MatMatModMmcmc (W, B, B, m);
      MatMatModMmcmc (W, W, W, m);
      n /= 2;
   }
}



/*-------------------------------------------------------------------------*/

static double U01mcmc(RngStream g)
{
   long k;
   double p1, p2, u;

   /* Component 1 */
   p1 = a12 * g->Cg[1] - a13n * g->Cg[0];
   k = p1 / m1;
   p1 -= k * m1;
   if (p1 < 0.0)
      p1 += m1;
   g->Cg[0] = g->Cg[1];
   g->Cg[1] = g->Cg[2];
   g->Cg[2] = p1;

   /* Component 2 */
   p2 = a21 * g->Cg[5] - a23n * g->Cg[3];
   k = p2 / m2;
   p2 -= k * m2;
   if (p2 < 0.0)
      p2 += m2;
   g->Cg[3] = g->Cg[4];
   g->Cg[4] = g->Cg[5];
   g->Cg[5] = p2;

   /* Combination */
   u = ((p1 > p2) ? (p1 - p2) * norm : (p1 - p2 + m1) * norm);
   return (g->Anti) ? (1 - u) : u;
}



/*-------------------------------------------------------------------------*/

static double U01mcmcd (RngStream g)
{
   double u;
   u = U01mcmc(g);
   if (g->Anti == 0) {
      u += U01mcmc(g) * fact;
      return (u < 1.0) ? u : (u - 1.0);
   } else {
      /* Don't forget that U01mcmc() returns 1 - u in the antithetic case */
      u += (U01mcmc(g) - 1.0) * fact;
      return (u < 0.0) ? u + 1.0 : u;
   }
}


/*-------------------------------------------------------------------------*/

static int CheckSeedmcmc (unsigned long seed[6])
{
   /* Check that the seeds are legitimate values. Returns 0 if legal seeds,
     -1 otherwise */
   int i;

   for (i = 0; i < 3; ++i) {
      if (seed[i] >= m1) {
	 fprintf (stderr, "****************************************\n"
		 "ERROR: Seed[%1d] >= m1, Seed is not set.\n"
		 "****************************************\n\n", i);
	 return (-1);
       }
   }
   for (i = 3; i < 6; ++i) {
      if (seed[i] >= m2) {
	 fprintf (stderr, "****************************************\n"
		 "ERROR: Seed[%1d] >= m1, Seed is not set.\n"
		 "****************************************\n\n", i);
	 return (-1);
       }
   }
   if (seed[0] == 0 && seed[1] == 0 && seed[2] == 0) {
      fprintf (stderr, "****************************\n"
	      "ERROR: First 3 seeds = 0.\n"
	      "****************************\n\n");
      return (-1);
   }
   if (seed[3] == 0 && seed[4] == 0 && seed[5] == 0) {
      fprintf (stderr, "****************************\n"
	      "ERROR: Last 3 seeds = 0.\n"
	      "****************************\n\n");
      return (-1);
   }

   return 0;
}



/*---------------------------------------------------------------------*/
/* Public part.                                                        */
/*---------------------------------------------------------------------*/


RngStream RngStream_CreateStreammcmc (const char name[])
{
   int i;
   RngStream g;
   size_t len = strlen (name);

   g = (RngStream) malloc (sizeof (struct RngStream_InfoState));
   if (g == NULL) {
      printf ("RngStream_CreateStreammcmc: No more memory\n\n");
      exit (EXIT_FAILURE);
   }
   g->name = (char *) malloc ((len + 1) * sizeof (char));
   strncpy (g->name, name, len + 1); 
   g->Anti = 0;
   g->IncPrec = 0;

   for (i = 0; i < 6; ++i) {
      g->Bg[i] = g->Cg[i] = g->Ig[i] = nextSeed[i];
   }
   MatVecModMmcmc (A1p127, nextSeed, nextSeed, m1);
   MatVecModMmcmc (A2p127, &nextSeed[3], &nextSeed[3], m2);
   return g;
}

/*-------------------------------------------------------------------------*/

void RngStream_DeleteStreammcmc (RngStream * p)
{
   if (*p == NULL)
      return;
   if ((*p)->name != NULL)
      free ((*p)->name);
   free (*p);
   *p = NULL;
}

/*-------------------------------------------------------------------------*/

void RngStream_ResetStartStreammcmc (RngStream g)
{
   int i;
   for (i = 0; i < 6; ++i)
      g->Cg[i] = g->Bg[i] = g->Ig[i];
}

/*-------------------------------------------------------------------------*/

void RngStream_ResetNextSubstreammcmc (RngStream g)
{
   int i;
   MatVecModMmcmc (A1p76, g->Bg, g->Bg, m1);
   MatVecModMmcmc (A2p76, &g->Bg[3], &g->Bg[3], m2);
   for (i = 0; i < 6; ++i)
      g->Cg[i] = g->Bg[i];
}

/*-------------------------------------------------------------------------*/

void RngStream_ResetStartSubstreammcmc (RngStream g)
{
   int i;
   for (i = 0; i < 6; ++i)
      g->Cg[i] = g->Bg[i];
}

/*-------------------------------------------------------------------------*/

void RngStream_SetPackageSeedmcmc (unsigned long seed[6])
{
   int i;
   if (CheckSeedmcmc (seed))
      exit (EXIT_FAILURE);
   for (i = 0; i < 6; ++i)
      nextSeed[i] = seed[i];
}

/*-------------------------------------------------------------------------*/

void RngStream_SetSeedmcmc (RngStream g, unsigned long seed[6])
{
   int i;
   if (CheckSeedmcmc (seed))
      exit (EXIT_FAILURE);
   for (i = 0; i < 6; ++i)
      g->Cg[i] = g->Bg[i] = g->Ig[i] = seed[i];
}

/*-------------------------------------------------------------------------*/

void RngStream_AdvanceStatemcmc (RngStream g, long e, long c)
{
   double B1[3][3], C1[3][3], B2[3][3], C2[3][3];

   if (e > 0) {
      MatTwoPowModMmcmc (A1p0, B1, m1, e);
      MatTwoPowModMmcmc (A2p0, B2, m2, e);
   } else if (e < 0) {
      MatTwoPowModMmcmc (InvA1, B1, m1, -e);
      MatTwoPowModMmcmc (InvA2, B2, m2, -e);
   }

   if (c >= 0) {
      MatPowModMmcmc (A1p0, C1, m1, c);
      MatPowModMmcmc (A2p0, C2, m2, c);
   } else {
      MatPowModMmcmc (InvA1, C1, m1, -c);
      MatPowModMmcmc (InvA2, C2, m2, -c);
   }

   if (e) {
      MatMatModMmcmc (B1, C1, C1, m1);
      MatMatModMmcmc (B2, C2, C2, m2);
   }

   MatVecModMmcmc (C1, g->Cg, g->Cg, m1);
   MatVecModMmcmc (C2, &g->Cg[3], &g->Cg[3], m2);
}

/*-------------------------------------------------------------------------*/

void RngStream_GetStatemcmc (RngStream g, unsigned long seed[6])
{
   int i;
   for (i = 0; i < 6; ++i)
      seed[i] = g->Cg[i];
}

/*-------------------------------------------------------------------------*/

void RngStream_WriteStatemcmc (RngStream g)
{
   int i;
   if (g == NULL)
      return;
   printf ("The current state of the Rngstream");
   if (strlen (g->name) > 0)
      printf (" %s", g->name);
   printf (":\n   Cg = { ");

   for (i = 0; i < 5; i++) {
      printf ("%lu, ", (unsigned long) g->Cg[i]);
   }
   printf ("%lu }\n\n", (unsigned long) g->Cg[5]);
}

/*-------------------------------------------------------------------------*/

void RngStream_WriteStateFullmcmc (RngStream g)
{
   int i;
   if (g == NULL)
      return;
   printf ("The RngStream");
   if (strlen (g->name) > 0)
      printf (" %s", g->name);
   printf (":\n   Anti = %s\n", (g->Anti ? "true" : "false"));
   printf ("   IncPrec = %s\n", (g->IncPrec ? "true" : "false"));

   printf ("   Ig = { ");
   for (i = 0; i < 5; i++) {
      printf ("%lu, ", (unsigned long) (g->Ig[i]));
   }
   printf ("%lu }\n", (unsigned long) g->Ig[5]);

   printf ("   Bg = { ");
   for (i = 0; i < 5; i++) {
      printf ("%lu, ", (unsigned long) (g->Bg[i]));
   }
   printf ("%lu }\n", (unsigned long) g->Bg[5]);

   printf ("   Cg = { ");
   for (i = 0; i < 5; i++) {
      printf ("%lu, ", (unsigned long) (g->Cg[i]));
   }
   printf ("%lu }\n\n", (unsigned long) g->Cg[5]);
}

/*-------------------------------------------------------------------------*/

void RngStream_IncreasedPrecismcmc (RngStream g, int incp)
{
   g->IncPrec = incp;
}

/*-------------------------------------------------------------------------*/

void RngStream_SetAntitheticmcmc (RngStream g, int a)
{
   g->Anti = a;
}

/*-------------------------------------------------------------------------*/

double RngStream_RandU01mcmc (RngStream g)
{
   if (g->IncPrec)
      return U01mcmcd (g);
   else
      return U01mcmc (g);
}

/*-------------------------------------------------------------------------*/

long RngStream_RandIntmcmc (RngStream g, long i, long j)
{
   return i + (long) ((j - i + 1) * RngStream_RandU01mcmc (g));
}

/*-------------------------------------------------------------------------*/

time_t time(time_t *t);

/*-------------------------------------------------------------------------*/


double versemblanca_haplomcmc (double *freq,matriu_int *codi_haplo_cromo1,matriu_int *codi_haplo_cromo2,vec_int *llargada_vec,int nindiv,double *pesos,int *npes,int nlocus){

   int i,j,l,m,llargada,a,mod,p,ll;
   double *llargades,vertotal,ver,nova_log;
  
   llargades=(double *)malloc(pow(4,nlocus)*sizeof(double));

   ver=0.;
   nova_log=0.;
   a=0;
  
     
   for(i=0;i<nindiv;i++){
      vertotal=0.;
      llargada=0;
      ll=llargada_vec->v[i];
      
      for(l=0;l<npes[i];l++){
          llargades[npes[i]-1-l]=(ll/pow(10,npes[i]-1-l));
          p=pow(10,npes[i]-1-l);
          mod=ll%p;
          ll=mod;
      }
          
      m=0;
      while(m<npes[i]){
         
          
          for(j=0;j<(int)llargades[m];j++){
           
             if(codi_haplo_cromo2->val[i][j]==codi_haplo_cromo1->val[i][j]) {
                ver=freq[codi_haplo_cromo1->val[i][j+llargada]]*freq[codi_haplo_cromo2->val[i][j+llargada]];
             }else{
                ver=2*freq[codi_haplo_cromo1->val[i][j+llargada]]*freq[codi_haplo_cromo2->val[i][j+llargada]];
             }

             vertotal=vertotal+pesos[a]*ver;
                
          }
          
          a=a+1;
          llargada=llargada+(int)llargades[m];
          m=m+1;
     
      }
      nova_log=nova_log+log(vertotal);     
    
   }
   
   return nova_log;
   
 }
 
/*-------------------------------------------------------------------------*/

int catmcmc (RngStream t,double *p,int llarg)
{

   int i,lloc;
   double *interv;
   double suma,u;
 
   suma=0;
   lloc=0;
   u=RngStream_RandU01mcmc(t);
   interv=(double *)malloc((llarg+1)*sizeof(double));
   for(i=0;i<llarg+1;i++){
        interv[i]=suma;   
        suma=suma+p[i];
   }
  
   i=llarg-1;
   do{ 
      if(u>interv[i])lloc=i;
      i=i-1;
   }while (lloc==0 && i>0);
   free(interv);
   return lloc;
   
   }


/*-------------------------------------------------------------------------*/


void assigna_codimcmc (vec_int *llargada_vec,matriu_int *codi_haplo_cromo1,matriu_int *codi_haplo_cromo2,
                   double *freq,RngStream t,vec_int *haplo1,vec_int *haplo2,int dosexpnl,int nindiv)
{  
  
   double *frequencia; 
   double sumafreq;
   int i,j,llarg,lloc;
  
   
   frequencia=(double *)malloc((dosexpnl*dosexpnl)*sizeof(double));
 
  
  for(i=0;i<dosexpnl*dosexpnl;i++){
      frequencia[i]=-9;
  }  
  sumafreq=0.;   
  for(i=0;i<nindiv;i++){
      llarg=llargada_vec->v[i];
      sumafreq=0.;
      if(llarg!=1){
         for(j=0;j<llarg;j++){
             frequencia[j]=freq[codi_haplo_cromo1->val[i][j]] * freq[codi_haplo_cromo2->val[i][j]];
             sumafreq=sumafreq+frequencia[j];
         }
         for(j=0;j<llarg;j++){
             frequencia[j]=frequencia[j]/sumafreq;
         }
         lloc=catmcmc(t,frequencia,llarg);
         haplo1->v[i]=codi_haplo_cromo1->val[i][lloc];
         haplo2->v[i]=codi_haplo_cromo2->val[i][lloc];
      }else{
         haplo1->v[i]=codi_haplo_cromo1->val[i][0];
         haplo2->v[i]=codi_haplo_cromo2->val[i][0];
      }
    
  }
  free(frequencia); 

}

/*-------------------------------------------------------------------------*/

double maximmcmc (int *interesa,double *freq,int dosexpnl)
{

   int i,max,a;
 
   a=0;
   max=0;
   for(i=0;i<dosexpnl;i++){
      if(interesa[i]==1){
        if(a==0){   
          max=i;
          a=a+1;
        }else{
          if(freq[i]>freq[max]){
          max=i;
          }
        }
      }
   }

   return max;
   
}

/*-------------------------------------------------------------------------*/


void fer_dummysmcmc (int max_freq,vec_int *haplo1,vec_int *haplo2,int tamany,
                 int *interesa, int *interesa2, matriu_doub *dummy,int nindiv,
                 int pos_rares,int model,matriu_doub *covars, int ncovars,int ncoeff,int inters,int pheno,int *interscov)
{ 
   int i,j,k,a,trobat,dosindiv;
   double quant_int; 
  
 
   a=0;
   dosindiv=2*nindiv;
   
 
   for(i=0;i<dosindiv;i++){
      for(j=0;j<ncoeff;j++){ 
         if(j==0){
           dummy->val2[i][j]=1.;
         }else{
           dummy->val2[i][j]=0.;
         }
      }
   }

   

  if(model==0){ /*additive model*/
    for(i=0;i<nindiv;i++){
      j=0;
      trobat=0;
      if(interesa[haplo1->v[i]]==1){
        do{
          if(interesa2[j]==haplo1->v[i]){
        
            dummy->val2[i][j+1]=1.;  
            
            trobat=1;    
          }
          if(haplo1->v[i]==max_freq){
            trobat=1;
          }
          j=j+1;
        }while(trobat!=1);
      }else{
        dummy->val2[i][pos_rares]=1.; 
      }
     
      j=0;
      trobat=0;   
      if(interesa[haplo2->v[i]]==1){
        do{
           if(interesa2[j]==haplo2->v[i]){
         
             dummy->val2[i+nindiv][j+1]=1.;  
             
             trobat=1;    
           }
           if(haplo2->v[i]==max_freq){
             trobat=1;
           }
           j=j+1;
        }while(trobat!=1);
      }else{ 
        dummy->val2[i+nindiv][pos_rares]=1.;   
      }
   }    
  } 
   if (model==1){ /*Dominant model*/
    for(i=0;i<nindiv;i++){
        j=0;
        trobat=0;      
        if((interesa[haplo1->v[i]]==1)&&(interesa[haplo2->v[i]]==1)){ 
           if (haplo1->v[i]==haplo2->v[i]){ /*homozygote*/
            do{
               if(interesa2[j]==haplo2->v[i]){
                
                  dummy->val2[i][j+1]=1.;
                  dummy->val2[i+nindiv][j+1]=0.;  
                  
                  trobat=1;    
               }
               if(haplo1->v[i]==max_freq){
                  trobat=1;
               }
               j=j+1; 
                       
            }while(trobat!=1);              
           }else{ /*heterozygote*/
              do{
                 if(interesa2[j]==haplo1->v[i]){
                  
                    dummy->val2[i][j+1]=1.;  
                   
                    trobat=1;    
                 }
                 if(haplo1->v[i]==max_freq){
                    trobat=1;
                 } 
                 j=j+1;
              }while(trobat!=1); 
              j=0;
              trobat=0;
              do{
                 if(interesa2[j]==haplo2->v[i]){
                
                    dummy->val2[i+nindiv][j+1]=1.;  
                  
                    trobat=1;    
                 }
                 if(haplo2->v[i]==max_freq){
                     trobat=1;
                 }
                 j=j+1;
              }while(trobat!=1);                              
           }
        }
        
                  
        if((interesa[haplo1->v[i]]!=1)&&(interesa[haplo2->v[i]]!=1)){ 
           dummy->val2[i][pos_rares]=1.; 
           dummy->val2[i+nindiv][pos_rares]=0.;
        } 
        if((interesa[haplo1->v[i]]==1)&&(interesa[haplo2->v[i]]!=1)){
          do{
            if(interesa2[j]==haplo1->v[i]){
             
               dummy->val2[i][j+1]=1.;  
            
               trobat=1;    
             }
             if(haplo1->v[i]==max_freq){
               trobat=1;
             }
             j=j+1;
          }while(trobat!=1);
          dummy->val2[i+nindiv][pos_rares]=1.;
        }     
     
        if((interesa[haplo1->v[i]]!=1)&&(interesa[haplo2->v[i]]==1)){
          do{
            if(interesa2[j]==haplo2->v[i]){
            
               dummy->val2[i+nindiv][j+1]=1.;  
            
               trobat=1;    
            }
            if(haplo2->v[i]==max_freq){
               trobat=1;
            }
            j=j+1;
          }while(trobat!=1);
          dummy->val2[i][pos_rares]=1.;   
       }
    
     } 
  } 
   
   
  if(model==2){ /*Recessive model*/ 
    for(i=0;i<nindiv;i++){
      j=0;
      trobat=0;    
      if((interesa[haplo1->v[i]]==1)&&(interesa[haplo2->v[i]]==1)){ 
        if (haplo1->v[i]==haplo2->v[i]){                   
            do{
               if(interesa2[j]==haplo2->v[i]){
                 
                  dummy->val2[i][j+1]=1.;
                  dummy->val2[i+nindiv][j+1]=0.;                    
                 
                  trobat=1;    
               }
               if(haplo1->v[i]==max_freq){
                  trobat=1;
               }
               j=j+1; 
                       
           }while(trobat!=1);                                                                                                                                                                                                                                                                                                                                                               
        }
      }          
      if((interesa[haplo1->v[i]]!=1)&&(interesa[haplo2->v[i]]!=1)){ 
          if(haplo1->v[i]==haplo2->v[i]){                                                                    
           dummy->val2[i][pos_rares]=1.;
           dummy->val2[i+nindiv][pos_rares]=0.; 
          }                                                            
      }   
    } 
  }
    
  for(i=0;i<nindiv;i++){
        for(j=0;j<ncovars;j++){
           dummy->val2[i][j+(tamany+1)]=covars->val2[i][j];
           dummy->val2[i+nindiv][j+(tamany+1)]=covars->val2[i][j];
        }
  }      

  quant_int=0.;
  for(i=0;i<ncovars;i++){
      quant_int=quant_int+interscov[j];
  }
  if (inters!=0){
      for(i=0;i<nindiv;i++){
             a=0;
  	     for(j=0;j<ncovars;j++){
                 if(interscov[j]==1){
                   for(k=0;k<tamany;k++){ 
                        dummy->val2[i][k+(tamany+1+ncovars)+a*tamany]=covars->val2[i][j]*dummy->val2[i][k+1];
           	        dummy->val2[i+nindiv][k+(tamany+1+ncovars)+a*tamany]=covars->val2[i][j]*dummy->val2[i+nindiv][k+1];
                    }
                    a=a+1;
                  } 
             }
      }
  }
  

}


/*-------------------------------------------------------------------------*/

void aleatmcmc (vec_doub *rn, RngStream t,int iter,int dist)
{
   int d;
   double x1,x2,lx;
  
   
     
   x1=RngStream_RandU01mcmc(t);
   x2=RngStream_RandU01mcmc(t);
   
   d=0;
   if(d==dist){/*0: uniform*/
     rn->v[0]= x1-0.5;
     rn->v[1]= x2-0.5; 
   }else{ /*1: normal*/
     lx=sqrt(-2*log(x1));
     rn->v[0]= lx*cos(PI*2*x2);
     rn->v[1]= lx*sin(PI*2*x2); 
   }
   
}


/*-------------------------------------------------------------------------*/



double prior_fun(double beta,double var,double mu)
{
       
double prior;
if(mu!=-9.){
   prior=-(0.5)*log(2*var*PI)-(((beta-mu)*(beta-mu))/(2*var));
}else{
   prior=0.;
}

return prior;       
              
       
}


/*-------------------------general likelihood------------------------------*/


double versemblanca (int *binary, double *beta, matriu_doub *haplo, int tamany, int nindiv, double *resp, int pheno,int act,double *var,double varc,int ncoeff,double *mu,int prior)
{
    double logvertot,k,xbeta,sigmados,e,b;
    int i,j,dosindiv; 
    
    
    logvertot=0.;
    dosindiv=2*nindiv;
    if (pheno==0){/*logit*/
       for(i=0;i<dosindiv;i++){
           xbeta=0.;
           for(j=0;j<ncoeff;j++){        
               xbeta=xbeta+beta[j]*haplo->val2[i][j];
           }
           logvertot=logvertot + xbeta*binary[i] - log(1.+exp(xbeta));
       }
       if ((prior==1)&(act<tamany)){
          logvertot=logvertot+prior_fun(beta[act],var[act],mu[act]);          
       }
       
    } 
    if (pheno==1){/*weibull*/
  
       k=beta[ncoeff-1];
       for(i=0;i<dosindiv;i++){
           xbeta=0.;
           for(j=0;j<ncoeff-1;j++){  
              xbeta=xbeta+beta[j]*haplo->val2[i][j];
            
           }
           e=exp(k);
           b=exp(xbeta); 
           if (binary[i]==0){
              logvertot=logvertot-b*pow(resp[i],e);
           }else{
                
              logvertot=logvertot+k+xbeta+(e-1)*log(resp[i])-b*pow(resp[i],e);
           }    
       }
       if ((prior==1)&(act<tamany)){
         logvertot=logvertot+prior_fun(beta[act],var[act],mu[act]);          
       }                       
    }
    if (pheno==2){/*gaussian*/
        sigmados=exp(beta[ncoeff-1]);
       
        for(i=0;i<dosindiv;i++){
            xbeta=0.;
            for(j=0;j<ncoeff-1;j++){  
            xbeta=xbeta+beta[j]*haplo->val2[i][j];
            }   
    
    logvertot=logvertot - (  ( ((resp[i]-xbeta)*(resp[i]-xbeta))   / (2.* sigmados) + 0.5*log(2.*PI*sigmados)));     

        } 
        if ((prior==1)&(act<tamany)){
           logvertot=logvertot+prior_fun(beta[act],var[act],mu[act]); 
                     
        }                                   
    }
       
   return logvertot;        
       
}


/*--------------------------slice sampler functions---------------------------*/


void intervals_pheno_doubling (double *extrems,RngStream t,double y,int *pheno_double,double *beta,matriu_doub *dummy,int tamany, int nindiv,int i,double w,double *var, double *temps,int pheno,double varc,int ncoeff,double *mu,int prior){
   
double u,L,R,p,k,v,l1,l2,b;



p=2.;

b=beta[i];
u=RngStream_RandU01mcmc(t);   
L=beta[i]-w*u;
R=L+w;
k=p;
beta[i]=L;
l1=versemblanca(pheno_double,beta,dummy,tamany,nindiv,temps,pheno,i,var,varc,ncoeff,mu,prior);
beta[i]=R;
l2=versemblanca(pheno_double,beta,dummy,tamany,nindiv,temps,pheno,i,var,varc,ncoeff,mu,prior);




while(k>0&&(y<l1||y<l2)){
  
  v=RngStream_RandU01mcmc(t); 
  if (v<0.5){
     L=L-(R-L);
     beta[i]=L;
     l1=versemblanca(pheno_double,beta,dummy,tamany,nindiv,temps,pheno,i,var,varc,ncoeff,mu,prior);
   
  }else{
     R=R+(R-L);
     beta[i]=R;
     l2=versemblanca(pheno_double,beta,dummy,tamany,nindiv,temps,pheno,i,var,varc,ncoeff,mu,prior); 
     
  }   
  k=k-1;
  
}
beta[i]=b;
extrems[0]=L;
extrems[1]=R;

}



/*-------------------------------------------------------------------------*/

void intervals_pheno_steppingout (double *extrems,RngStream t,double y,int *pheno_double,double *beta,matriu_doub *dummy,int tamany, int nindiv,int i,double w,double *var,int pheno,double *temps,double varc,int ncoeff,double *mu,int prior){
     
double u,L,R,k,v,l1,l2,b;
int j;
int m;



m=10;

b=beta[i];
u=RngStream_RandU01mcmc(t);   
L=beta[i]-w*u;
R=L+w;
v=RngStream_RandU01mcmc(t); 
j=floor(m*v);
k=(m-1)-j;


beta[i]=L;
l1=versemblanca(pheno_double,beta,dummy,tamany,nindiv,temps,pheno,i,var,varc,ncoeff,mu,prior);

beta[i]=R;
l2=versemblanca(pheno_double,beta,dummy,tamany,nindiv,temps,pheno,i,var,varc,ncoeff,mu,prior);


while(j>0&&(y<l1)){
  
  L=L-w;
  j=j-1;
  beta[i]=L;
  l1=versemblanca(pheno_double,beta,dummy,tamany,nindiv,temps,pheno,i,var,varc,ncoeff,mu,prior);

}

while(k>0&&(y<l2)){
  
  R=R+w;
  k=k-1;
  beta[i]=R;
  l2=versemblanca(pheno_double,beta,dummy,tamany,nindiv,temps,pheno,i,var,varc,ncoeff,mu,prior);


}

 
beta[i]=b;
extrems[0]=L;
extrems[1]=R;

}



/*-------------------------------------------------------------------------*/


double slice_pheno(int *pheno_double,double *beta,matriu_doub *dummy,int tamany,int nindiv,RngStream t,int i,double w,double *var,double *cont,int type_pheno,double varc,int ncoeff,double *mu,int prior,int only_freq){
       
double *extrems;
vec_doub r_aleat;
double fxcan,u,v,r,xcan,xact,y,z,L,R;
int exit_ok,exit_error,compt,iter;


iter=0;

extrems=(double *)malloc((2)*sizeof(double));
r_aleat.v=(double *)malloc((2)*sizeof(double));


xact=beta[i];
y=versemblanca(pheno_double,beta,dummy,tamany,nindiv,cont,type_pheno,i,var,varc,ncoeff,mu,prior);


v=RngStream_RandU01mcmc(t); 
r=RngStream_RandU01mcmc(t); 
z=y-(-log(r));

if (type_pheno==0){
   intervals_pheno_steppingout(extrems,t,z,pheno_double,beta,dummy,tamany,nindiv,i,w,var,type_pheno,cont,varc,ncoeff,mu,prior); 
}else{
    if (type_pheno==1){
        intervals_pheno_doubling(extrems,t,z,pheno_double,beta,dummy,tamany,nindiv,i,w,var,cont,type_pheno,varc,ncoeff,mu,prior);
    }else{
        if (type_pheno==2){
            intervals_pheno_doubling(extrems,t,z,pheno_double,beta,dummy,tamany,nindiv,i,w,var,cont,type_pheno,varc,ncoeff,mu,prior);
        }                       
    }    
}
exit_ok=0;
exit_error=0;
compt=0;

L=extrems[0];
R=extrems[1];
do{
 
 u=RngStream_RandU01mcmc(t); 
 xcan=L+u*(R-L);
 beta[i]=xcan;
 fxcan=versemblanca(pheno_double,beta,dummy,tamany,nindiv,cont,type_pheno,i,var,varc,ncoeff,mu,prior);
 if (z<fxcan){
     exit_ok=1;
 }else{
     exit_ok=0;
     if(xcan<xact){
        L=xcan;
     }else{   
        R=xcan;
     }         
                   
 }

 compt=compt+1;
 
  if (compt==1000){
      exit_error=1;
      exit_ok=1;

  } 
}while(exit_ok==0);

  if ((exit_error==1)&&(only_freq==0)) {
      printf("ERROR: The implemented method is not suitable for these data, the algorithm not converge. \n");
      exit(0);
  }
      

free(extrems); 
return xcan;      
}


/*-------------------------------------------------------------------------*/

void Gibbs_pheno(int *pheno_double,double *beta,matriu_doub *dummy,int tamany,RngStream t,int nindiv,double *meanw,double *var,double *temps,int type_pheno,double varc,int ncoeff,double *mu,int prior,double *versem_bic,int only_freq)

{
  double y,ver;
  int i;
  for(i=0;i<ncoeff;i++){
      y=slice_pheno(pheno_double,beta,dummy,tamany,nindiv,t,i,meanw[i],var,temps,type_pheno,varc,ncoeff,mu,prior,only_freq);
      if((y!=-9)&&(type_pheno!=2)){
       beta[i]=y;      
      }
      if (i==(ncoeff-1)){
         ver=versemblanca(pheno_double,beta,dummy,tamany,nindiv,temps,type_pheno,i,var,varc,ncoeff,mu,prior);
         *versem_bic=ver;
      }

  }
 
}
 

/*-------------------------------main--------------------------------------*/
  
    
    void mcmc(
         int *numindiv,        /*number of subjects*/
         int *numindivexp,
         double *weights,
         int *numlocus,        /*number of locus*/
         int *burn_in,         /*first burnin*/
         int *burn_in_haplo,   /*burnin for haplo chain*/
         int *burn_in_pheno,   /*burnin for logit chain*/
         int *total_iter,      /*iters for average*/
         int *genotypes,        
         int *phenotype,       /*vector of phenotypes: case-control or censure indicator*/
         int *max_haplo,       /*max number of haplotypes for memory*/
         int  *distribution,   /*distribution to sampler in RW, 0 unif or 1 normal*/
         int  *type_pheno,     /*0 binary or 1 survival 2 continuous*/
         double *freqmin,      /*under freq-min, haplotypes are rares*/
         double *devhaplo,     /*Deviation for haplotypes chain*/
         double *devlogit,     /*Deviation for logit chain*/
         int *lag_number,      /*lag number for mean average*/
         double *time_var,     /*continuous variable for survival analysis or linear regression*/
         int *mem_error,       /*memory error due to number of individuals(1) or nlocus(2)*/
         double *res_freq,
         double *res_se_freq,
         double *res_coeff,
         double *res_se_coeff,
         double *haplos_int,
         int *llista_haplos,
         int *n_coeff,
         int  *type_model,     /*0 additive,1 dominant, 2 recessive */      
         double *var_cont,
         int *num_covar,
         double *covariates,   /*vector of covariates*/
         int *interactions,    /*number of covariates to make interaction*/
         int *int_covars,      /*indicator of covariate interaction*/
         int *priorval,        /*indicator of prior values*/
         double *mu_prior,
         double *var_prior,
         int *haplo1_R,        /*vectors of haplotypes codes*/
         int *haplo2_R,
         int *n_pairs,         /*number of haplotye pairs per individual*/
         int *verbose,         /*text showed during execution 0=non text 1=some messages 2= all messages*/
         double *versem_max,    /*maximum value of the likelihood to calculate BIC*/
         int *onlyfreq,
         char **id_outhaplo
        
       )
    {
 

         int nindiv,nlocus,dist,burnin,burnin_logit,tot_iter,pheno,model,ncovars,verb,geno;
         double freq_min,dev_haplo,dev_logit,varc;
         
     
        
         matriu_doub dummy;
         matriu_doub covars;
         vec_int haplo1,haplo2;
         vec_doub r;
         matriu_int codi_haplo_cromo1;
         matriu_int codi_haplo_cromo2;
         vec_int llargada_vec;
        
      
         RngStream t;
         unsigned long seed[6];
         
         int i,j,burnin_haplo,dosindiv,lag;         
         int *na,*heterozigots,*pheno_double;         
         int *interesa,*interesa2;
         double *temps,*freq,*nova_freq,*mitjana,*variancia,*mediana,*suma_hmediana;
         double *suma_h,*suma_hq,*suma_l,*suma_lq;
         double haplopost_cur,haplopost_can,sum,logversemblanca;
         int iter,noacceptat,max_freq,tamany,a,dosexpnl,dosexpmenysu;
         double u,g,e,guarda,guardamediana;
         double ratio_haplo;
         double rare,no_rare_suma;
         double *beta,*nova_beta,*rbeta,*mitjana_beta,*variancia_beta,*beta_ant,*w,*meanw,*meanw2;         
         int cont,pos_rares;
         
         double *batchmeans,*batchmeans_q,beta_transf;
         int nbatch,batch,inters;
         int ncoeff,prior;
         double *pesos,suma_pes,*mu,*varp,versem_bic2,versem_bic1_aux;
         int *npes,nindivexp,*interscov,iterd,maxpairs,llargada_ant,only_freq;

         char outhaplo[50]="outhaplo";
         char outhaplo2[50]="outhaplo2";
         char ext[5]=".txt";
         char **id;
                 
       
         
         FILE *sortida,*sortida2;

          
         nindiv=*numindiv;
         nindivexp=*numindivexp;
         nlocus=*numlocus;
         dist=*distribution;
         burnin=*burn_in;
         burnin_haplo=*burn_in_haplo;
         burnin_logit=*burn_in_pheno;
         tot_iter=*total_iter;
         
         pheno=*type_pheno;
         model=*type_model;
         freq_min=*freqmin;
         dev_haplo=*devhaplo;
         dev_logit=*devlogit;
        
         dosindiv=2*nindiv;
         dosexpnl=pow(2,nlocus);
         dosexpmenysu=pow(2,nlocus-1);
         lag=*lag_number;
         varc=*var_cont;
         ncovars=*num_covar;
         inters=*interactions;

         prior=*priorval;
         maxpairs=pow(2,3*(nlocus-1));
         verb=*verbose;
         versem_bic1_aux=0.; 
         geno=*genotypes;
         only_freq=*onlyfreq;
        

         versem_bic2=0.;
         ncoeff=0.;
         pos_rares=0;
         guarda=0;
         max_freq=0;
         sortida=fopen("a.txt","w");
         fclose(sortida);
         sortida2=fopen("b.txt","w");
         fclose(sortida2);

         
         
               
	 if (verb==2){        
		printf("number of indiv = %i \n",nindiv);
                printf("number of locus = %i \n",nlocus);
                printf("burnin = %i \n",burnin);
                printf("burnin for haplo chain = %i \n",burnin_haplo);
                printf("burnin for model chain = %i \n",burnin_logit);
                printf("total number of iters = %i \n",tot_iter); 			
		printf("type of pheno = %i \n",pheno);
                printf("freq min = %lf \n",freq_min);
                printf("deviation for haplo chain = %lf \n",dev_haplo);
                printf("number of total possible haplotypes = %i \n",dosexpnl);
                printf("lag = %i \n",lag);
                printf("number of covars =%i \n",ncovars);
             
	 }

         /****************memory alloc*****************************************/
   
         dummy.val2=(double **)malloc(dosindiv*sizeof(double*));
         covars.val2=(double **)malloc(dosindiv*sizeof(double*));
         codi_haplo_cromo1.val=(int **)malloc(nindiv*sizeof(int*));
         codi_haplo_cromo2.val=(int **)malloc(nindiv*sizeof(int*));
         haplo1.v=(int *)malloc(nindiv*sizeof(int));
         haplo2.v=(int *)malloc(nindiv*sizeof(int));
         llargada_vec.v=(int *)malloc(nindiv*sizeof(int));
         r.v=(double *)malloc((2)*sizeof(double));
         freq=(double *)malloc((dosexpnl)*sizeof(double));
         nova_freq=(double *)malloc((dosexpnl)*sizeof(double));
         interesa=(int *)malloc((dosexpnl)*sizeof(int));
         interesa2=(int *)malloc((dosexpnl)*sizeof(int));
         mitjana=(double *)malloc((dosexpnl+ncovars+dosexpnl*ncovars+1)*sizeof(double));
         suma_h=(double *)malloc((dosexpnl)*sizeof(double));
         suma_hq=(double *)malloc((dosexpnl)*sizeof(double));
         mediana=(double *)malloc((dosexpnl)*sizeof(double));
         suma_hmediana=(double *)malloc((dosexpnl)*sizeof(double));
         suma_l=(double *)malloc((dosexpnl+ncovars+dosexpnl*ncovars+1)*sizeof(double));
         suma_lq=(double *)malloc((dosexpnl+ncovars+dosexpnl*ncovars+1)*sizeof(double));
         beta=(double *)malloc((dosexpnl+ncovars+dosexpnl*ncovars+1)*sizeof(double));
         beta_ant=(double *)malloc((dosexpnl+ncovars+dosexpnl*ncovars+1)*sizeof(double));
         rbeta=(double *)malloc((dosexpnl+ncovars+dosexpnl*ncovars+1)*sizeof(double));
         nova_beta=(double *)malloc((dosexpnl+ncovars+dosexpnl*ncovars+1)*sizeof(double));
         mitjana_beta=(double *)malloc((dosexpnl+ncovars+dosexpnl*ncovars+1)*sizeof(double));
         variancia=(double *)malloc((dosexpnl+ncovars+dosexpnl*ncovars+1)*sizeof(double));
         variancia_beta=(double *)malloc((dosexpnl+ncovars+dosexpnl*ncovars+1)*sizeof(double));
         na=(int *)malloc((nindiv)*sizeof(int));
         heterozigots=(int *)malloc((nindiv)*sizeof(int));
         pheno_double=(int *)malloc((dosindiv)*sizeof(int));
         temps=(double *)malloc((dosindiv)*sizeof(double));
         batchmeans=(double *)malloc((dosexpnl+ncovars+dosexpnl*ncovars+1)*sizeof(double));
         batchmeans_q=(double *)malloc((dosexpnl+ncovars+dosexpnl*ncovars+1)*sizeof(double));
         w=(double *)malloc((2000)*sizeof(double));
         meanw=(double *)malloc((2000)*sizeof(double));
         meanw2=(double *)malloc((2000)*sizeof(double));
         pesos=(double *)malloc((nindivexp)*sizeof(double));
         npes=(int *)malloc((nindiv)*sizeof(int));
         interscov=(int *)malloc((ncovars)*sizeof(int));
         mu=(double *)malloc((dosexpnl)*sizeof(double));
         varp=(double *)malloc((dosexpnl)*sizeof(double));
         id=(char **)malloc(1*sizeof(char*));
         id[0]=(char*)malloc(26*sizeof(char));

       
        /* 
         */
         
        
         /*strcpy(id,id_outhaplo);*/
         
         for(i=0;i<25;i++){
              id[0][i]=id_outhaplo[0][i];                         
              
         }
         printf("id=%s \n",id[0]);
          id[0][25]='\0';
         
                   
         strcat (outhaplo,id[0]);
         strcat (outhaplo,ext);
         strcat (outhaplo2,id[0]); 
         strcat (outhaplo2,ext);
         printf("nom outhaplo=%s \n",outhaplo);


         for(i=0;i<nindivexp;i++){
             pesos[i]=weights[i];                                     
         }
         a=0;
         i=0;
         do{
            if(pesos[i]==1.){
               npes[a]=1;
               i=i+npes[a];
               a=a+1;               
            }else{
               suma_pes=0;
               j=i;
               do{ 
                 suma_pes=suma_pes+pesos[j]; 
                 j=j+1;                                 
               }while(suma_pes<1.);               
               if(suma_pes==1.){
                  npes[a]=j-i;
               }else{
                  npes[a]=j-i-1;     
               }                  
               i=i+npes[a];
               a=a+1;
            }                 
         }while(i<nindivexp);         
         a=0;
         i=0;
         *mem_error=0;
         if ((dummy.val2==NULL)||(codi_haplo_cromo1.val==NULL)||
            (codi_haplo_cromo2.val==NULL)||(haplo1.v==NULL)||
            (haplo2.v==NULL)||(llargada_vec.v==NULL)){
                                                      
            *mem_error=1; 
            
         }else{   
            if((freq==NULL)||(nova_freq==NULL)||(interesa==NULL)||
                 (interesa2==NULL)||(mitjana==NULL)||(suma_h==NULL)||(mediana==NULL)||(suma_hmediana==NULL)
                 ||(suma_hq==NULL)||(suma_l==NULL)||(suma_lq==NULL)){
                                                                     
                *mem_error=2;
                
            }else{
                  for(i=0;i<dosindiv;i++){
                      dummy.val2[i]=(double*)malloc((dosexpnl+ncovars+dosexpnl*ncovars+1)*sizeof(double));
                      if(dummy.val2[i]==NULL)*mem_error=2;
                  } 
                  for(i=0;i<dosindiv;i++){
                      covars.val2[i]=(double*)malloc((ncovars)*sizeof(double));
                      if(covars.val2[i]==NULL)*mem_error=2;
                  }  
                  for(i=0;i<nindiv;i++){
                      codi_haplo_cromo1.val[i]=(int*)malloc((maxpairs)*sizeof(int));
                      codi_haplo_cromo2.val[i]=(int*)malloc((maxpairs)*sizeof(int));
                      if( codi_haplo_cromo1.val[i]==NULL||codi_haplo_cromo2.val[i]==NULL){ *mem_error=2;}
                  }                  
                  
            } 
         }
        
         nbatch=40;
         batch=0;        
         cont=0;
         
            /*seed for random generator*/

            srand (time(0));
            for(i=0;i<6;i++){
                seed[i]=rand();
            }  
            t=RngStream_CreateStreammcmc("a");
            RngStream_SetSeedmcmc(t,seed); 
            
            for(i=0;i<nindiv;i++){
                 na[i]=0;
                 heterozigots[i]=0;
            }
            
            if((*mem_error!=1)&&(*mem_error!=2)){
               for(i=0;i<nindiv;i++){
                   for(j=0;j<ncovars;j++){
                       covars.val2[i][j]=covariates[j+i*ncovars];                    
                   }
                                      
               } 
              
            for (i=0;i<ncovars;i++){
                 interscov[i]=int_covars[i];
            }
            for(i=0;i<dosexpnl;i++){
                   mu[i]=mu_prior[i];
                   varp[i]=var_prior[i];
            }
          
            /*binary phenotype data*/

            for(i=0;i<nindiv;i++){
                pheno_double[i]=phenotype[i];
                pheno_double[nindiv+i]=phenotype[i];
            }
            /*continuous phenotype data*/
            
               for(i=0;i<nindiv;i++){
                   temps[i]=time_var[i];
                   temps[nindiv+i]=time_var[i];
               }               

            /*initialize haplo variables*/

            for(i=0;i<nindiv;i++){
                for(j=0;j<maxpairs;j++){
                    codi_haplo_cromo1.val[i][j]=-9;
                    codi_haplo_cromo2.val[i][j]=-9;  
                }
            }    

            
            for(i=0;i<nindiv;i++){
                llargada_vec.v[i]=n_pairs[i];
            }
            llargada_ant=0;
            for(i=0;i<nindiv;i++){
                for(j=0;j<llargada_vec.v[i];j++){
                    codi_haplo_cromo1.val[i][j]=haplo1_R[j+llargada_ant];
                    codi_haplo_cromo2.val[i][j]=haplo2_R[j+llargada_ant];                      
                  
                }
                llargada_ant=llargada_ant+llargada_vec.v[i];
            }             
           
            haplo1.llargada=nindiv;
            haplo2.llargada=nindiv;
            llargada_vec.llargada=nindiv;
            r.llargada=2;
            r.v[0]=-9;
            r.v[1]=-9;
        
          
            for(i=0;i<dosexpnl;i++){ 
                freq[i]=1.0/dosexpnl;
            }
      
       
            logversemblanca=versemblanca_haplomcmc(freq,&codi_haplo_cromo1,&codi_haplo_cromo2,&llargada_vec,nindiv,pesos,npes,nlocus);
            haplopost_cur=logversemblanca;
            noacceptat=0;
            tamany=0; 
           
            /* MCMC haplo*/
           
            for(iter=0; iter< (tot_iter+burnin+burnin_haplo+burnin_logit); iter++){
                if (iter==0){
                    if (only_freq==1){
                        sortida2=fopen(outhaplo2,"w");
                        fprintf(sortida2,"%s","iter");
                        for(i=0;i<dosexpnl;i++){
                            fprintf(sortida2," %s%i","haplo.",i+1);
                        }
                        fprintf(sortida2," \n"); 	
                    }              
                    
                    if (((verb==1)||(verb==2))&&(only_freq==0)){
                         printf("Processing burn in period...\n");
                    }
                    
                }
                
                if ((iter==burnin+burnin_haplo+burnin_logit)&&(only_freq==0)){
                   if ((verb==1)||(verb==2)){ 
                   printf("End of burn in period. Processing iterations...\n");
                   }
                }
                if (iter%1000==0) {
                  iterd=iter/lag;
                    if (verb==2){
                    printf("iter=%i \n",iterd);
                    }
                }
                sum=0;
                for(i=0;i<dosexpnl;i++){
                    if(i%2==0) aleatmcmc(&r,t,iter,dist);
                       e=log(freq[i]/(1-freq[i]));
                       g=dev_haplo*r.v[(i%2==0)] + e; 
                       nova_freq[i]=1./(1.+exp(-g));
                       sum=sum+nova_freq[i];

                }
                
                for(i=0;i<dosexpnl;i++) {  
                       nova_freq[i]=nova_freq[i]/sum;
                }
                
                haplopost_can=versemblanca_haplomcmc(nova_freq,&codi_haplo_cromo1,&codi_haplo_cromo2,&llargada_vec,nindiv,pesos,npes,nlocus);
                     
               
                ratio_haplo=exp(haplopost_can-haplopost_cur);
                u=RngStream_RandU01mcmc(t);
                if((u)<ratio_haplo){
                   for(i=0;i<dosexpnl;i++){
                       freq[i]=nova_freq[i];
                   }
                   haplopost_cur=haplopost_can;
                }

                if((only_freq==1)&&((iter>=burnin) && iter<(burnin+burnin_haplo))&&((iter+1)%lag==0)){
                    fprintf(sortida2,"%i",iter);
                    for(i=0;i<dosexpnl;i++){
                           fprintf(sortida2," %8.6f",freq[i]);
                          
                    }
                    fprintf(sortida2," \n"); 	                   
                }
                
             if((iter==burnin+burnin_haplo)&&(only_freq==1)){
            
                    fclose(sortida2);

             }                    
                /*compute frequent haplotypes*/               
            

                if(iter==burnin){       
                   for(i=0;i<dosexpnl;i++){
                       interesa[i]=0;
                       suma_h[i]=0.;
                       suma_hq[i]=0.;
                   }
                   guarda=0.;
                }

                /*add freq for average */
              
                if(iter>=burnin && iter<(burnin+burnin_haplo)){     
                   guarda=guarda+1;
                   for(i=0;i<dosexpnl;i++){
                       suma_h[i]=suma_h[i]+freq[i];
                   }
                }
                  
                if(iter==(burnin+burnin_haplo)){         
                   for(i=0;i<dosexpnl;i++){
                       suma_h[i]=suma_h[i]/guarda;
          
                       if(suma_h[i]>freq_min){
                          interesa[i]=1;
                          tamany=tamany+1;
                       }  
                    }
                  
                   /*update here to add a new likelihood*/

                   if ((pheno==0)||(pheno==2)){
                   pos_rares=tamany;          
                   }    
                   if (pheno==1){                       
                   pos_rares=tamany;
                   }
  
                   ncoeff=tamany+1+ncovars;

                   if ((pheno==2)||(pheno==1)){
		   ncoeff=ncoeff +1 ; 
		   }
 		   if (inters!=0){
		   ncoeff=ncoeff+tamany*inters;
                   }
                   if ((verb==2)&&(only_freq==0)){
                   printf("Number of haplotypes with frequency higher than freqmin = %i \n",tamany);
                   }
                   if ((tamany==1)&&(only_freq==0)){
                   printf("Only one haplotype over rare treshold. Model coefficients could not be interpretable. \n"); 
		   }
                   if ((verb==2)&&(only_freq==0)){
                   printf("Number of parameters for the markov chain = %i \n",ncoeff);
                   }
               
                   
                   guarda=0.;
                   a=0.;
                   max_freq=maximmcmc(interesa,suma_h,dosexpnl); 
                   for(i=0;i<dosexpnl;i++){
                       if(interesa[i]==1){
                          if(i!=max_freq){
                             interesa2[a]=i;
                             a=a+1;
                          }  
                       }  
                   } 
	           for(i=0;i<dosexpnl;i++){
                       suma_h[i]=0.;
                   }
                   for(i=0;i<ncoeff;i++){
                       aleatmcmc(&r,t,iter,dist);
                       beta[i]=0.2;
                       beta_ant[i]=0.2;
                       suma_l[i]=0.;
                       suma_lq[i]=0.;
                       batchmeans[i]=0.;
                       batchmeans_q[i]=0.;
                       meanw[i]=0.5;
                   }
                   
                   
                      sortida=fopen(outhaplo,"w");
                      fprintf(sortida,"%s","iter");
                      for(i=0;i<dosexpnl;i++){
                        if(interesa[i]==1){  
                           fprintf(sortida," %s%i","h",i);
                        }
                      }              
         	      fprintf(sortida," %s","b-int");                    
                      for(i=0;i<(pos_rares-1);i++){
                        fprintf(sortida," %s%i","b",interesa2[i]);
                      }               
                      fprintf(sortida," rare"); 
                      if(ncovars==0){
                        if(pheno==0) fprintf(sortida," \n"); 
                        if((pheno==1)||(pheno==2)) fprintf(sortida," param\n");
                      }else{
                        for(i=0;i<ncovars;i++){  
                           fprintf(sortida," %s%i","cov",i); 
                        }                                                      		 
                        if(inters!=0){                          
			  for(i=0;i<(tamany)*inters;i++){  
                              fprintf(sortida," %s%i","int-cov-hap",i); 
                          }                                                      
                        }
                        if((pheno==1)||(pheno==2)){
                           fprintf(sortida," param");
                        }
                        fprintf(sortida," \n"); 				                                      			      }                         
               
                     }
                   
               
          
               /*begin the call to Gibbs*/    

               if ((iter>=(burnin+burnin_haplo))&&(only_freq==0)){ 
                   assigna_codimcmc(&llargada_vec, &codi_haplo_cromo1, &codi_haplo_cromo2, freq, t, &haplo1,  		
                   &haplo2,dosexpnl,nindiv);   
                   fer_dummysmcmc(max_freq,&haplo1,&haplo2,tamany,interesa,interesa2,&dummy,nindiv,pos_rares,model,&covars,ncovars,ncoeff,inters,pheno,interscov);            
                   Gibbs_pheno(pheno_double,beta,&dummy,tamany,t,nindiv,meanw,varp,temps,pheno,varc,ncoeff,mu,prior,&versem_bic1_aux,only_freq);
        
                   if (iter==burnin+burnin_haplo){
                       versem_bic2=versem_bic1_aux;
                   }
                   if (iter>=(burnin+burnin_haplo+1)){
                       if (versem_bic2<versem_bic1_aux){
                           versem_bic2=versem_bic1_aux;
                       }
                   }                                                
               }
     
               /*saving haplotype chain*/ 

                if((iter==(burnin+burnin_haplo+burnin_logit)&&(iter+1)%lag==0)&&(only_freq==0)){
                   for(i=0;i<ncoeff;i++){                   
                       suma_l[i]=0.;
                       suma_lq[i]=0.;
                       meanw2[i]=0.;                                              
                   }
                }   

                if(iter>=(burnin+burnin_haplo+burnin_logit)&& ((iter+1)%lag==0)&&(only_freq==0)){
                  guarda=guarda+1;
                  for(i=0;i<dosexpnl;i++){
                      if(interesa[i]==1){
                         suma_h[i]=suma_h[i]+freq[i];
                         if(iter==burnin+burnin_haplo+burnin_logit+(tot_iter/2)-1) {
                            suma_hmediana[i]=suma_h[i];
                            guardamediana=guarda;
                         }    
                         suma_hq[i]=suma_hq[i]+freq[i]*freq[i]; 
                      }
                  }
                  
                  
                  fprintf(sortida,"%i",iter);
                  for(i=0;i<dosexpnl;i++){
                       if(interesa[i]==1){
                           fprintf(sortida," %8.6f",freq[i]);
                       }   
                  }
      
                  /*saving chain for model coefficients*/

                  for(i=0;i<ncoeff;i++){
                               
                     if ((pheno==1)&&(i==ncoeff-1)){
                         beta_transf=exp(beta[i]);                     
                     }else{
                         beta_transf=beta[i];                     
                     }    
                     suma_l[i]=suma_l[i]+beta_transf;
  	             suma_lq[i]=suma_lq[i]+beta_transf*beta_transf;
                     fprintf(sortida," %8.6f",beta_transf);
                  }
                   
                  if(iter<=((burnin+burnin_haplo+burnin_logit)+4999)&&(iter+1)%lag==0){
                      for(i=0;i<ncoeff;i++){
                          w[i]=fabs(beta[i]-beta_ant[i]); 
                          meanw2[i]=meanw2[i]+w[i];
                      } 
                      cont=cont+1;                       
                  }
                  if((iter==((burnin+burnin_haplo+burnin_logit)+4999))&&(iter+1)%lag==0){
                      for(i=0;i<ncoeff;i++){
                          meanw2[i]=meanw2[i]/cont;                             
                      }    
                      for(i=0;i<ncoeff;i++){
                          meanw[i]=meanw2[i];  
                      }                                                    
                      for(i=0;i<ncoeff;i++){
                         beta_ant[i]=beta[i];
                      }                          
                                                                           
                  }
                  fprintf(sortida,"\n");                                   
               }                                                    
            
          }/*for iter*/
    
           /*computing haplotype means*/
          
            for(i=0;i<dosexpnl;i++){
                mitjana[i]=(suma_h[i]/guarda);
                variancia[i]=sqrt((suma_hq[i]/guarda)-(mitjana[i]*mitjana[i]));  
            }                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      

            /*computing means for model coefficients*/      

            for(i=0;i<ncoeff;i++){
                mitjana_beta[i]=suma_l[i]/guarda;
                variancia_beta[i]=sqrt(guarda/(guarda-1)*((suma_lq[i]/guarda)-(mitjana_beta[i]*mitjana_beta[i])));
            }

            /*computing frequency of rares*/

            no_rare_suma=0;
            for(i=0;i<dosexpnl;i++){ 
                if(interesa[i]==1){ 
                   no_rare_suma=no_rare_suma+mitjana[i];
                }                                
            }
            rare=1.-no_rare_suma;  
     
            /*results*/
     
            for(i=0;i<dosexpnl;i++){
                if(interesa[i]==1){
                   res_freq[i]=mitjana[i];
                   res_se_freq[i]=variancia[i];                        
                }   
            }
            for(i=0;i<ncoeff;i++){
                res_coeff[i]=mitjana_beta[i];
                res_se_coeff[i]=variancia_beta[i];
            }
            for(i=0;i<dosexpnl;i++){
                haplos_int[i]=interesa[i];                        
                                    
            }
            for(i=0;i<dosexpnl;i++){
                for(j=0;j<nlocus;j++){
                    llista_haplos[j+i*nlocus]=0;                        
                                  
                }
            }
            *n_coeff=ncoeff;
            *versem_max=versem_bic2;
           
     
    
           
              
          

            for(i=0;i<dosindiv;i++){
                free(dummy.val2[i]);
                free(covars.val2[i]);
            }  
    
            for(i=0;i<nindiv;i++){
                free(codi_haplo_cromo1.val[i]);
                free(codi_haplo_cromo2.val[i]);
            }

              
             
   fclose(sortida);
   free(dummy.val2);
   free(covars.val2);
   free(codi_haplo_cromo1.val);
   free(codi_haplo_cromo2.val);
   free(haplo1.v);
   free(haplo2.v);
   free(llargada_vec.v);
   free(r.v);
   free(freq);
   free(nova_freq);
   free(interesa);
   free(interesa2);
   free(mitjana);
   free(suma_h);
   free(suma_hq);
   free(mediana);
   free(suma_hmediana);
   free(suma_l);
   free(suma_lq);
   free(beta);
   free(beta_ant);
   free(rbeta);
   free(nova_beta);
   free(mitjana_beta);
   free(variancia_beta);
   free(variancia);
   free(na);
   free(heterozigots);
   free(pheno_double);
   free(temps);
   free(batchmeans);
   free(batchmeans_q);
   free(w);
   free(meanw);
   free(meanw2);
   free(pesos);
   free(npes);
   free(interscov);
   free(mu);
   free(varp);   
 }
}





