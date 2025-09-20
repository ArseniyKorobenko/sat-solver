// UI: or, usr_clause, solve, reset, attempts, vLit, pLit. gQ[0..n]=solution
#define _CRT_SECURE_NO_WARNINGS
#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
typedef float F;typedef void V;
typedef int I; typedef unsigned long long U,u64; I _=-1u/2;
#define PF "%d"
#define _(e...) ({e;}) /* a b=args e=body n=name r=result */
#define i(a,e) _(I $=a;I i=0;W(i<$){e;i++;}$!=i)
#define j(a,e) _(I $=a;I j=0;W(j<$){e;j++;}$!=j)
#define i1(a,e) _(I $=a;I i=1;W(i<$){e;i++;}$!=i)
#define k(a,b,e) _(I $=b;I k=a;W(k<$){e;k++;}$!=k)
#define r(a,e...) _(typeof(a)r=a;e;r)
#define j_ (*j++)
#define i_ (*i++)
#define N I n
#define ai a[i]
#define aj a[j]
#define ak a[k]
#define W while
#define R return
#define B break;
#define AS(a) assert(a);
#define AL(a) (I)(sizeof(a)/sizeof*(a))
#define swp(a,b) r(a,a=b;b=r)
#define pf(e...) printf(e);
#define D(a) pf(#a"="PF"\n",a);
I mn(I a,I b){R a<b?a:b;} I mx(I a,I b){R a>b?a:b;}
I rng(V){static u64 r=12345;r^=r<<13;r^=r>>7;r^=r<<17;R r&_;}

enum{LITS=0x10000,LITC=0x100000,VARS=LITS/2,VARB=VARS/64};
typedef unsigned Lit;
typedef struct{I c;Lit bl;}Watcher;
// W[lit]=watchers; L=lit arena; C=clauses; Q=queue[q.head]=lit;
// A[var]assigned,val,seen,heap; Q[Lv[n]]backjmp; V[var]=cause,lvl,activity;
// blockers redundant? wv.ai[0]+wv.ai[1]-v
struct{N,a[VARS];} gLv;
struct{N,cap;Watcher*a;} gW[LITS];
struct{N,head;Lit a[VARS];} gQ;
struct{N,a[VARS],b[VARS];} gH; // heap p=(i-1)/2 l=i*2+1 r=i*2+2
struct{N,temp,t,x,end;Lit a[LITC];} gC; // temp=start; t=top; x=next
struct{u64 a[VARB],v[VARB],sn[VARB];} gA;
struct{N,max,c[VARS],lv[VARS];F a[VARS];} gV;
I attempts=10000;
#define or(a...) _(int r[]={a};usr_clause(AL(r),r));
#define v(n,a) b##n(gA.a,v/2)
#define ANL(b) AS(sizeof(b.a)==sizeof(V*)||b.n<AL(b.a));
#define p(b,v) r(b.n++,ANL(b);b.a[r]=v)
#define rALLV(e) {i(gQ.n,if(!gH.bi)r(gQ.ai/2,e));i(gH.n,r(gH.ai,e));}
#define wv gW[v]
#define cn gC.a[cr]
#define ca (gC.a+cr+1)
#define c02(e) {Lit v=*ca^1,b=ca[1];{e;}v=ca[1]^1;b=*ca;{e;}}
V init(V){AS(gV.max<VARS); gC.t=gC.x=gC.temp=0x10000;gC.end=0x50000;}
// V reset(V){gLv.n=0;gQ.n=0;gV.n=0;gH.n=0;} // TODO:
V bset(u64*a,N){a[n/64]|=1ull<<n%64;} I bget(u64*a,N){R a[n/64]>>n%64&1;}
V bclr(u64*a,N){a[n/64]&=~(1ull<<n%64);} F1(pLit,a&1?-a/2:a/2) F1(vLit,r(a<0?-a*2|1:a*2,AS(r<LITS)))
V hp_up(I i){I v=gH.ai,k=(i-1)/2; W(i&&gV.a[v]>gV.a[gH.ak])
 {gH.ai=gH.ak;gH.b[gH.ak]=i+1;i=k;k=(k-1)/2;}gH.ai=v;gH.b[v]=i+1;}
V hp_down(I i){I*a=gH.a;I v=ai;W(i*2+1<gH.n){I j=i*2+1,r=i*2+2;
 I k=r<gH.n&&gV.a[ar]>gV.a[aj]?r:j;if(gV.a[ak]<=gV.a[v])B;ai=ak;gH.b[ai]=i+1;i=k;}ai=v;}
V hp_put(I v){v/=2;if(gH.b[v])R;gH.b[v]=gH.n;hp_up(p(gH,v));}
I hp_pop(){R gH.n?2*r(*gH.a,*gH.a=gH.a[--gH.n];gH.b[*gH.a]=1;gH.b[r]=0; if(gH.n>1)hp_down(0)):0;}
V dump(V){pf("<Heap>\n")i(gH.n,pf("%d^%.1f  ",gH.ai,gV.a[gH.ai]));
    pf("\n<Queue>\n")i(gQ.n,pf("%d=>%d|%d^%.1f  ",gV.c[gQ.ai/2],pLit(gQ.ai),gV.lv[gQ.ai/2],gV.a[gQ.ai/2]));
    // pf("\n<Clauses>")i(gC.n,pf("\nc%d: ",i)j(gC.ai.n,pf("%3d ",pLit(gC.ai.aj))));
    pf("\n<Assigns>")i(gQ.n,pf("\n% d",pLit(gQ.ai)));
    pf("\n<Vars> ")rALLV(pf("\n% d wb: ",pLit(r*2))j(gW[r*2].n,pf("%3d|%d ",gW[r*2].aj.c,pLit(gW[r*2].aj.bl))));
    pf("\n<-Vars> ")rALLV(pf("\n% d wb: ",pLit(r*2+1))j(gW[r*2+1].n,pf("%3d|%d ",gW[r*2+1].aj.c,pLit(gW[r*2+1].aj.bl))));
    pf("\n----------END DUMP----------\n")}
V assign(Lit v){AS(!v(get,a));v(set,a);if(v&1)v(set,v);}
I val(Lit v){R v(get,a)&&v(get,v)==v%2;}
Lit deq(){AS(gQ.head<gQ.n);R gQ.a[gQ.head++];}
V enq(Lit v,I cr){assign(v);gV.c[v/2]=cr;gV.lv[v/2]=gLv.n;p(gQ,v);}
V watch1(I cr,I v,I b){D(cr)D(v)D(b)if(wv.n>=wv.cap){wv.cap=mx(8,wv.cap*2);
 wv.a=realloc(wv.a,wv.cap*sizeof(*wv.a));}wv.a[wv.n].c=cr;wv.a[wv.n++].bl=b;}
V watch(I cr){c02(watch1(cr,v,b))}I locked(I cr){R val(*ca)&&gV.c[*ca/2]==cr;}
// V unwatch(I cr){c02(i(wv.n,if(wv.ai.c==cr){swp(wv.ai,wv.a[wv.n]);wv.n--;B}));if(locked(cr))gV.c[*ca/2]=_;}
V rewatch(I cr,I new){c02(i(wv.n,if(wv.ai.c==cr){wv.ai.c=new;B}));if(locked(cr))gV.c[*ca/2]=new;}
I make_space(N){AS(n);I j=1;W(gC.x<=gC.t+n&&(j=gC.a[gC.x])){if(locked(gC.x)&&gLv.n){
 rewatch(gC.x,gC.t);i(j+1,gC.a[gC.t++]=gC.a[gC.x++]);}else{rewatch(gC.x,_);gC.x+=j+1;}}
 R r(gC.t,gC.t+=n+1;k(gC.t,gC.x,gC.ak=0);if(!j){gC.t=gC.x=gC.end<gC.t?gC.temp:gC.t;}D(r));}
I clause(I cr){if(cn==1){enq(*ca,_);gC.n=cr;R _;}if(cn<9)R cr; // cr in PERM
 R r(make_space(cn),i(cn+1,gC.a[r+i]=gC.a[cr+i]);gC.n=cr;watch(r));}
I usr_clause(N,int*a){R r(p(gC,n),i(n,I v=vLit(ai);AS(v<LITS);gV.max=mx(gV.max,v/2);p(gC,v);hp_put(v));watch(r));}
// TODO: minimization
// TODO: resets
// TODO: interleave gA.av
V back_to(I lv){if(lv>=gLv.n)R;I i;for(i=gQ.n-1;i>=gLv.a[lv];i--)
 {I v=gQ.ai;v(clr,a);v(clr,v);hp_put(v);}gQ.n=gQ.head=i+1; gLv.n=lv;}
Lit branch(V){Lit v;do{if(gH.n==0)R 0;v=hp_pop();}W(v(get,a));R v|rng()<_/2;}
V vbump(I i){gV.ai++;if(gH.bi)hp_up(gH.bi-1);}V vdecay(V){i(gV.max,gV.ai*=0.998f);}
I prop(V){W(gQ.head<gQ.n){
 Lit v=deq();if(!wv.a)continue; Watcher*i,*j,*end=wv.a+wv.n;
 for(i=j=wv.a;i!=end;){if(i->c==_){i_;continue;}
  if(val(i->bl)){j_=i_;continue;}I cr=i->c;Lit*a=ca;
  if(*a==(v^1))swp(*a,a[1]);if(*a!=i_.bl&&val(*a)){j_.bl=*a;continue;}
  if(k(2,cn,if(!val(ak^1)){swp(a[1],ak);watch1(cr,a[1],*a);B}))
   continue;j_.bl=*a;if(val(*a^1)){W(i!=end)j_=i_;wv.n-=i-j;R cr;}
  enq(*a,cr);}wv.n-=i-j;}R _;}
I analyze(I cr,I*lv){I r=p(gC,0);p(gC,0);I deps=0,i=gQ.n;Lit v=0;
 do{AS(cr!=_);AS(!v||v==*ca);k(!!v,cn,Lit v=ca[k];if(!v(get,sn)&&gV.lv[v/2]){
   vbump(v/2);v(set,sn);if(gV.lv[v/2]<gLv.n)p(gC,v);else deps++;});
  W(v=gQ.a[--i],!v(get,sn));cr=gV.c[v/2];v(clr,sn);deps--;}W(deps>0);
 cr=r;cn=gC.n-cr-1;Lit*a=ca;*a=v^1;i(cn,gA.sn[ai/128]=0);if(cn==1){*lv=0;R cr;}
 i=1;k(2,cn,if(gV.lv[ak/2]>gV.lv[ai/2])i=k);*lv=gV.lv[ai/2];swp(a[1],ai);R cr;}
I solve(){init();i(attempts,I conf=prop();  D(i);D(conf);dump();
 if(conf!=_){pf("conflict!\n")if(gLv.n==0)R 0;I lv=0;I cr=analyze(conf,&lv);
  back_to(lv);cr=clause(cr);if(cr!=_)enq(*ca,cr);vdecay();
 }else{Lit v=branch();if(!v)R 1;p(gLv,gQ.n);enq(v,_);}
 );back_to(0);R _;}
// wiki cdcl
V t2(V) {
 or(1,4)
 or(1,-3,-8)
 or(1,8,12)
 or(2,11)
 or(-7,-3,9)
 or(-7,8,-9)
 or(7,8,-10)
 or(7,10,-12)
 or(1,-4,8)
 or(1,-4,-8)
 dump();
 D(solve());dump();
}

// https://www.youtube.com/watch?v=DIcRFQ2xzlA&t=394s
V t1(V) {
 or(-1,2)
 or(-1,-3)
 or(-2)
 or(2,3)
 or(1,2,-3,4)
 or(2,-4)
 P(solve());dump();
}
V t3(V) {
 or(-1,2,3)
 or(1,3,4)
 or(1,3,-4)
 or(1,-3,4)
 or(1,-3,-4)
 or(-2,-3,4)
 or(-1,2,-3)
 or(-1,-2,3)
 P(solve());dump();
}
V t4(V) {
 or(-1,-2,3)
 or(1,-2,3)
 or(-3,4)
 or(-3,-4)
 or(-1,3,4)
 or(-1,2,-4)
 or(2,3,-4)
 or(1,2,4)
 P(solve());dump();
}


int main(V){
 t2();
}
