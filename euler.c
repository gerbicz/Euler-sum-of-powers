// Written by Robert Gerbicz from Hungary
// Searching for solutions of the Euler(6,2,5) systems: a^6+b^6=c^6+d^6+e^6+f^6+g^6 by a new method
// One of them of c,d,e,f,g can be zero and/or one of them of a,b can be zero.
//
// Version 1.0
//

#include <stdio.h>
#include <stdlib.h>
#include <time.h>

unsigned long int powmod6(unsigned long int a, unsigned long int p)
{
  unsigned long long int K,h=a;
  
  K=(h*h)%p;
  K=(K*h)%p;
  K=(K*K)%p;
  
  return K;
}

int main (int argc, char *argv[])  {

   unsigned long int Range=117649;  // this is 7^6, the same as power7
   unsigned long int p=117659;  // p is prime, p>Range and p==2 mod 3
   unsigned long int *remp;
   unsigned long int *Inversep;
   unsigned long int start_rem_p=0;
   unsigned long int end_rem_p=p-1;
   unsigned long int primes[5]={100000007,100000037,100000039,100000049,100000073}; // sufficient for Range=117649

   unsigned long int a,b,c,d,e,f,g,h,i,j,k,l,m,n,nextpos,np,num,num2,pos,pre_p,pre_q,pre_r,prm,s,st,start_f,test,u,w;
   signed long int w2,w3;

   unsigned long int A[2],numb[2],temp[2],duo[512];
   unsigned long int *R,*L;
   unsigned long int table_size_L=1100000;
   unsigned long int table_size_R=12000000;
   unsigned long int q=4200013;  // q is prime
   unsigned long int *remq;
   unsigned long int r=1000000007;  // r is prime
   unsigned long int *remr;
   unsigned long int power7=117649;  // this is 7^6
   unsigned long int *rempower7;
   unsigned long int *Inversepower7;
   unsigned long int *triplets;

   unsigned long int percent,update;

   time_t seconds;
   
   L=(unsigned long int*) (malloc) (table_size_L*sizeof(unsigned long int));

   R=(unsigned long int*) (malloc) (table_size_R*sizeof(unsigned long int));

   triplets=(unsigned long int*) (malloc) ((3*table_size_R/2)*sizeof(unsigned long int));

   rempower7=(unsigned long int*) (malloc) (power7*sizeof(unsigned long int));
   Inversepower7=(unsigned long int*) (malloc) (power7*sizeof(unsigned long int));

   remp=(unsigned long int*) (malloc) (p*sizeof(unsigned long int));
   Inversep=(unsigned long int*) (malloc) (p*sizeof(unsigned long int));

   remq=(unsigned long int*) (malloc) (Range*sizeof(unsigned long int));

   remr=(unsigned long int*) (malloc) (Range*sizeof(unsigned long int));

   for(i=0;i<Range;i++)  {
       remq[i]=powmod6(i,q);
       remr[i]=powmod6(i,r);
   }  

   for(i=0;i<p;i++)  Inversep[i]=p;
   for(i=0;i<p;i++)  {
       u=powmod6(i,p);
       remp[i]=u;
       Inversep[u]=i;
   }

   for(i=0;i<power7;i++) Inversepower7[i]=0;
   for(i=0;i<power7;i++)  {
       u=powmod6(i,power7);
       rempower7[i]=u;
       if(u>0) Inversepower7[u+Inversepower7[u-1]]=i,Inversepower7[u-1]++;
   }

   for(i=start_rem_p;i<=end_rem_p;i++)  {
   // e^6+f^6+g^6==i mod p where e<=f<=g, 7|e,f,g and at least one of them is even
   // and at least one of them is divisible by 3
   // if e=0 then f>0
   printf("Testing remainder=%ld\n",i);
   printf("First stage.\n");
   seconds=time(NULL);
   update=0;
   nextpos=2*q;
       for(j=0;j<2*q;j+=2)  R[j]=0;
       for(e=0;e<Range;e+=7)  {
           if(e==0) start_f=7;
           else     start_f=e;
           pre_p=remp[e];
           pre_q=remq[e];
           pre_r=remr[e];
           for(f=start_f;f<Range;f+=7)  {
               u=pre_p+remp[f];
               if(u>=p)  u-=p;
               if(u<=i)  u=i-u;
               else      u=i+p-u;
               temp[0]=Inversep[u],temp[1]=p-temp[0];
               for(h=0;h<=1;h++)  {
               g=temp[h];
               if((g>=f)&&((g%7)==0)&&((e&1)+(f&1)+(g&1)<3)&&((e%3==0)||(f%3==0)||(g%3==0))&&(g<Range))  {
                     pos=pre_q+remq[f]+remq[g];
                     if(pos>=q)  pos-=q;
                     if(pos>=q)  pos-=q;
                     pos<<=1;
                     w=pre_r+remr[f]+remr[g];
                     if(w>=r)  w-=r;
                     if(w>=r)  w-=r;
                     w++;
                     if(R[pos]==0)  {
                        R[pos]=w;
                        R[pos+1]=0;
                        pos+=pos>>1;
                        triplets[pos]=e;
                        triplets[pos+1]=f;
                        triplets[pos+2]=g;
                     }
                     else {
                        while(R[pos+1]>0)  pos=R[pos+1];
                        R[pos+1]=nextpos;
                        R[nextpos]=w;
                        R[nextpos+1]=0;
                        pos=nextpos+(nextpos>>1);
                        triplets[pos]=e;
                        triplets[pos+1]=f;
                        triplets[pos+2]=g;
                        nextpos+=2;
                     }
                }
                }
             }
          }
    // finished the setup for right side
    printf("Complete the first stage. Time=%ld sec.\n",time(NULL)-seconds);
    seconds=time(NULL);
    printf("Second stage.\n");
          for(k=0;k<power7;k++)  {// a^6+b^6==k mod 117649
              if((k%7==1)||(k%7==2))  {
                  percent=(int) (double) 100.0*k/power7;
                  if(percent>update) update=percent,printf("    %ld percentage of the stage is complete. [ %ld sec. ]\r\r",update,time(NULL)-seconds),fflush(stdout);
                  for(l=0;l<4*p;l+=4)  L[l]=0;
                  nextpos=4*p;
                  if(k%7==1)  {
                     for(l=k;l<=k+5;l++)  {
                         a=Inversepower7[l];
                         pre_p=remp[a];
                         pre_q=remq[a];
                         pre_r=remr[a];
                         for(b=0;b<Range;b+=7)  {
                             pos=pre_p+remp[b];
                             if(pos>=p)  pos-=p;
                             pos<<=2;
                             s=pre_q+remq[b];
                             if(s>=q) s-=q;
                             w=pre_r+remr[b];
                             if(w>=r)  w-=r;
                             w++;
                             if(L[pos]==0)  {
                                L[pos]=w;
                                L[pos+1]=s;
                                L[pos+2]=0;
                             }
                             else {
                                if(L[pos+2]==0)  L[pos+2]=nextpos;
                                else             L[L[pos+3]+2]=nextpos;
                                L[pos+3]=nextpos;
                                L[nextpos]=w;
                                L[nextpos+1]=s;
                                L[nextpos+2]=0;
                                nextpos+=3;
                             }
                          }
                      }
                   }
                   else {
                      for(l=1;l<7;l++)  {
                           for(a=l;a<Range;a+=7)  {
                               st=rempower7[a];
                               if(k>=st)  st=k-st;
                               else       st=k+power7-st;
                               pre_p=remp[a];
                               pre_q=remq[a];
                               pre_r=remr[a];
                               for(m=st;m<=st+5;m++)  {
                                   b=Inversepower7[m];
                                   if(a>=b)  {  // symmetric rule
                                      pos=pre_p+remp[b];
                                      if(pos>=p) pos-=p;
                                      pos<<=2;
                                      s=pre_q+remq[b];
                                      if(s>=q) s-=q;
                                      w=pre_r+remr[b];
                                      if(w>=r) w-=r;
                                      w++;
                                      if(L[pos]==0)  {
                                         L[pos]=w;
                                         L[pos+1]=s;
                                         L[pos+2]=0;
                                      }
                                      else {
                                           if(L[pos+2]==0) L[pos+2]=nextpos;
                                           else            L[L[pos+3]+2]=nextpos;
                                           L[pos+3]=nextpos;
                                           L[nextpos]=w;
                                           L[nextpos+1]=s;
                                           L[nextpos+2]=0;
                                           nextpos+=3;
                                      }
                                   }
                                }
                             }
                        }
                     }
                     for(l=0;l<p;l++)  {  // a^6+b^6==l mod p, from this c^6+d^6==l-i mod p
                     // positions in duo array:
                     // (a^6+b^6)%r+1=duo[4*h]
                     // (a^6+b^6)%q=duo[4*h+1]
                     // (c^6+d^6)%r+1=duo[4*h+2]
                     // (c^6+d^6)%q=duo[4*h+3]
                         num=0,num2=2,test=0;
                         pos=l<<2;
                         if(L[pos]>0)  {
                               duo[num]=L[pos];
                               duo[num+1]=L[pos+1];
                               num+=4;
                               while(L[pos+2]>0)  {
                                     pos=L[pos+2];
                                     duo[num]=L[pos];
                                     duo[num+1]=L[pos+1];
                                     num+=4;
                               }
                          }
                          if(l>=i)  u=l-i;
                          else      u=l+p-i;
                          pos=u<<2;
                          if(L[pos]>0)  {
                               duo[num2]=L[pos];
                               duo[num2+1]=L[pos+1];
                               num2+=4;
                               while(L[pos+2]>0)  {
                                     pos=L[pos+2];
                                     duo[num2]=L[pos];
                                     duo[num2+1]=L[pos+1];
                                     num2+=4;
                               }
                           }
                           for(m=0;m<num;m+=4)  {
                               for(n=2;n<num2;n+=4)  {
                                   w3=duo[m+1]-duo[n+1];
                                   if(w3<0)  w3+=q;
                                   pos=w3<<1;
                                   if(R[pos]>0)  {
                                      w2=duo[m]-duo[n];
                                      if(w2<0)  w2+=r;
                                      w2++;
                                      if(R[pos]==w2)  test=1;
                                      while(R[pos+1]>0)  {
                                            pos=R[pos+1];
                                            if(R[pos]==w2)  test=1;
                                      }
                                   }
                                }
                           }
                        if(test)  {
                             // checking routine, this happens very rarely
                             // computation of the unsaved a,b,c,d values
                             numb[0]=0,numb[1]=0;
                             A[0]=l,A[1]=p+l-i;
                             if(A[1]>=p)  A[1]-=p;
                             // we overwrite the duo array
                             // positions in duo array:
                             // a=duo[4*h]
                             // b=duo[4*h+1]
                             // c=duo[4*h+2]
                             // d=duo[4*h+3]
                             for(n=0;n<=1;n++)  {
                                 for(a=0;a<Range;a++)  {
                                     u=remp[a];
                                     if(A[n]>=u)  u=A[n]-u;
                                     else         u=A[n]+p-u;
                                     temp[0]=Inversep[u],temp[1]=p-temp[0];
                                     for(m=0;m<=1;m++)  {
                                         b=temp[m];
                                         if((a>=b)&&(b<Range))  {
                                            u=rempower7[a]+rempower7[b];
                                            if(u>=power7) u-=power7;
                                            if(u==k)  {
                                                duo[4*numb[n]+2*n]=a;
                                                duo[4*numb[n]+2*n+1]=b;
                                                numb[n]++;
                                            }
                                         }
                                     }
                                 }
                             }
                             for(m=0;m<numb[0];m++)  {
                                 for(n=0;n<numb[1];n++)  {
                                     a=duo[4*m];
                                     b=duo[4*m+1];
                                     c=duo[4*n+2];
                                     d=duo[4*n+3];
                                     w2=(remq[a]+remq[b])%q;
                                     w2-=(remq[c]+remq[d])%q;
                                     if(w2<0) w2+=q;
                                     pos=w2<<1;
                                     if(R[pos]>0)  {
                                        s=(pos>>1)+pos;
                                        e=triplets[s];
                                        f=triplets[s+1];
                                        g=triplets[s+2];
                                        test=1;
                                        for(np=0;np<5;np++)  {
                                            prm=primes[np];
                                            w2=(powmod6(a,prm)+powmod6(b,prm))%prm;
                                            w2-=(powmod6(c,prm)+powmod6(d,prm)+powmod6(e,prm)+powmod6(f,prm)+powmod6(g,prm))%prm;
                                            if(w2<0) w2+=prm;
                                            if(w2!=0) test=0;
                                        }
                                        if(test)  {
                                           printf("Solution found! %ld^6+%ld^6=%ld^6+%ld^6+%ld^6+%ld^6+%ld^6                \n",a,b,c,d,e,f,g);
                                           FILE* out;
                                           out=fopen("euler_(6,2,5).txt","a+");
                                           fprintf(out,"Solution found! %ld^6+%ld^6=%ld^6+%ld^6+%ld^6+%ld^6+%ld^6\n",a,b,c,d,e,f,g);
                                           fclose(out);
                                        }
                                        while(R[pos+1]>0)  {
                                              pos=R[pos+1];
                                              s=(pos>>1)+pos;
                                              e=triplets[s];
                                              f=triplets[s+1];
                                              g=triplets[s+2];
                                              test=1;
                                              for(np=0;np<5;np++)  {
                                                  prm=primes[np];
                                                  w2=(powmod6(a,prm)+powmod6(b,prm))%prm;
                                                  w2-=(powmod6(c,prm)+powmod6(d,prm)+powmod6(e,prm)+powmod6(f,prm)+powmod6(g,prm))%prm;
                                                  if(w2<0) w2+=prm;
                                                  if(w2!=0) test=0;
                                              }
                                              if(test)  {
                                                 printf("Solution found! %ld^6+%ld^6=%ld^6+%ld^6+%ld^6+%ld^6+%ld^6                \n",a,b,c,d,e,f,g);
                                                 FILE* out;
                                                 out=fopen("euler_(6,2,5).txt","a+");
                                                 fprintf(out,"Solution found! %ld^6+%ld^6=%ld^6+%ld^6+%ld^6+%ld^6+%ld^6\n",a,b,c,d,e,f,g);
                                                 fclose(out);
                                              }
                                         }
                                     }
                                  }
                              }
                           }
                       }
                  }
            }
    // finished the second stage
    printf("Complete the second stage. Time=%ld sec.                \n",time(NULL)-seconds);
    }

    free(remp);
    free(Inversep);
    free(R);
    free(L);
    free(remq);
    free(remr);
    free(rempower7);
    free(Inversepower7);
    free(triplets);

   return 0;
}
