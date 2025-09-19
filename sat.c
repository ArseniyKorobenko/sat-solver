// UI: or, usr_clause, solve, reset, attempts, gQ[0..n]=solution
#define _CRT_SECURE_NO_WARNINGS
#include <stdio.h>
#include <assert.h>
#include <stdlib.h>
typedef float F;typedef void V;
typedef int I; typedef unsigned long long U,u64; 
#define PF "%d"
I MOD=1e9+7, _=-1u/2;
#define _(e...) ({e;}) /* a b=args e=body n=name r=result */
#define i(a,e) _(I $=a;I i=0;W(i<$){e;i++;}$!=i)
#define j(a,e) _(I $=a;I j=0;W(j<$){e;j++;}$!=j)
#define i1(a,e) _(I $=a;I i=1;W(i<$){e;i++;}$!=i)
#define k(a,b,e) _(I $=b;I k=a;W(k<$){e;k++;}$!=k)
#define r(a,e...) _(typeof(a)r=a;e;r)
#define j_ (*j++)
#define i_ (*i++)
#define A I a
#define N I n
#define ai a[i]
#define aj a[j]
#define ak a[k]
#define ar a[r]
#define aij a[i][j]
#define bi b[i]
#define R return
#define B break;
#define W while
#define AS(a) assert(a);
#define AL(a) (I)(sizeof(a)/sizeof*(a))
#define F1(n,e) I n(A){R _(e);}
#define F2(n,e) I n(A,I b){R _(e);}
#define s r(_,scanf(PF,&r))
#define pf(e...) printf(e);
#define swp(a,b) r(a,a=b;b=r)
#define D(a) pf(#a"="PF"\n",a);
F2(mn,a<b?a:b)    F1(P,pf(PF"\n",a)a)    F2(mx,a>b?a:b)    
I rng(V){static u64 r=12345;r^=r<<13;r^=r>>7;r^=r<<17;R r&_;}
enum{LITS=0x10000,LITC=0x100000,LITB=LITS/128};
typedef unsigned Lit;
typedef struct{I c;Lit bl;}Watcher;
// W[lit]=watchers; L=lit arena; C=clauses; Q=queue[q.head]=lit;
// A[var]assigned,val,seen,heap; Q[Lv[n]]backjmp; V[var]=cause,lvl,activity;
// blockers redundant? wv.ai[0]+wv.ai[1]-v
struct{N,a[LITS/2];} gLv;
struct{N,cap;Watcher*a;} gW[LITS];
struct{N,head;Lit a[LITS];} gQ;
struct{N,a[LITS/2],b[LITS/2];} gH; // heap p=(i-1)/2 l=i*2+1 r=i*2+2
struct{N,temp,i,x,end;Lit a[LITC],b[0x100];}gC; // temp=start; i=top; x=next
struct{N,c[LITS/2],lv[LITS/2];F a[LITS/2];} gV;
struct{u64 a[LITB],v[LITB],sn[LITB];} gA;
struct{I props,qn;}simp;
// V reset(V){gLv.n=0;gQ.n=0;gV.n=0;gH.n=0;} // TODO:
I attempts=10000,max_var=0;
#define wv gW[v]
#define cc gC.a[cr]
#define or(a...) _(int r[]={a};usr_clause(AL(r),r));
#define v(n,a) b##n(gA.a,v/2)
#define ANL(b) AS(sizeof(b.a)==sizeof(V*)||b.n<AL(b.a));
#define p(b,v) {ANL(b);b.a[b.n++]=v;}
#define rALLV(e) {i(gQ.n,if(!gH.bi)r(gQ.ai/2,e));i(gH.n,r(gH.ai,e));}
#define cn gC.a[cr]
#define ca (gC.a+cr+1)
#define c01(e) {Lit a=*ca,b=ca[1];e;swp(a,b);e;}
V init(V){
  gC.i=gC.x=gC.temp=0x10000;gC.end=0x50000;}
V bset(u64*a,N){a[n/64]|=1ull<<n%64;} I bget(u64*a,N){R a[n/64]>>n%64&1;}
V bclr(u64*a,N){a[n/64]&=~(1ull<<n%64);}
F1(pLit,a&1?-a/2:a/2) F1(vLit,r(a<0?-a*2|1:a*2,AS(r<LITS)))
V hp_down(I i){I*a=gH.a;I v=ai;W(i*2+1<gH.n){I j=i*2+1,r=i*2+2;
 I k=r<gH.n&&gV.a[ar]>gV.a[aj]?r:j;if(gV.a[ak]<=gV.a[v])B;ai=ak;gH.b[ai]=i+1;i=k;}ai=v;}
I hp_pop(){R gH.n?r(*gH.a,*gH.a=gH.a[--gH.n];gH.b[*gH.a]=1;gH.b[r]=0;
 if(gH.n>1)hp_down(0))*2:0;}
V hp_up(I i){I v=gH.ai,k=(i-1)/2;
 W(i&&gV.a[v]>gV.a[gH.ak]){gH.ai=gH.ak;gH.b[gH.ak]=i+1;i=k;k=(k-1)/2;}gH.ai=v;gH.b[v]=i+1;}
V hp_put(I v){v/=2;if(gH.b[v])R;gH.b[v]=gH.n;p(gH,v);hp_up(gH.n-1);}
V dump(V){pf("<Heap>\n")i(gH.n,pf("%d^%.1f  ",gH.ai,gV.a[gH.ai]));
    pf("\n<Queue>\n")i(gQ.n,pf("%d=>%d|%d^%.1f  ",gV.c[gQ.ai/2],pLit(gQ.ai),gV.lv[gQ.ai/2],gV.a[gQ.ai/2]));
    // pf("\n<Clauses>")i(gC.n,pf("\nc%d: ",i)j(gC.ai.n,pf("%3d ",pLit(gC.ai.aj))));
    pf("\n<Assigns>")i(gQ.n,pf("\n% d",gQ.ai));
    pf("\n<Vars> ")rALLV(pf("\n% d wb: ",pLit(r*2))j(gW[r*2].n,pf("%3d|%d ",gW[r*2].aj.c,pLit(gW[r*2].aj.bl))));
    pf("\n<-Vars> ")rALLV(pf("\n% d wb: ",pLit(r*2+1))j(gW[r*2+1].n,pf("%3d|%d ",gW[r*2+1].aj.c,pLit(gW[r*2+1].aj.bl))));
    pf("\n----------END DUMP----------\n")}
V watch(I cr,Lit v,Lit bl){v^=1;if(wv.n>=wv.cap){wv.cap=mx(8,wv.cap*2);
 wv.a=realloc(wv.a,wv.cap*sizeof(*wv.a));}Watcher w={.c=cr,.bl=bl};p(wv,w)}
V assign(Lit v){AS(!v(get,a));v(set,a);if(v&1)v(set,v);}
I val(Lit v){R v(get,a)&&v(get,v)==v%2;}
Lit deq(){AS(gQ.head<gQ.n);R gQ.a[gQ.head++];}
V enq(Lit v,I cr){assign(v);gV.c[v/2]=cr;gV.lv[v/2]=gLv.n;p(gQ,v)}
I locked(I cr){R val(*ca)&&gV.c[*ca/2]==cr;}
V unwatch(Lit v,I cr){i(wv.n,if(wv.ai.c==cr){swp(wv.ai,wv.a[wv.n]);wv.n--;B});}
V rewatch(Lit v,I a,I b){i(wv.n,if(wv.ai.c==a){wv.ai.c=b;B});}
V unclause(I cr){c01(unwatch(a,cr))if(locked(cr))gV.c[*ca/2]=_;}
I clause(N,Lit*a){I r,cr;AS(n);if(n==1)R enq(*a,_),_;if(n<9){r=gC.n;p(gC,n);i(n,p(gC,ai));}else{
 I j=1;W(gC.x<=gC.i+n&&(j=gC.a[gC.x])){cr=gC.x;if(locked(cr)&&gLv.n){
  r(gC.i,c01(rewatch(a,cr,r))gV.c[*ca/2]=r);i(j+1,gC.a[gC.i++]=gC.a[gC.x++]);
 }else{unclause(cr);gC.x+=j+1;}}r=gC.i;gC.a[gC.i++]=n;i(n,gC.a[gC.i++]=ai);
 k(gC.i,gC.x,gC.ak=0);if(!j){gC.i=gC.x=gC.i>gC.end?gC.temp:gC.i;}}cr=r;D(r)c01(watch(cr,a,b));R r;}
I usr_clause(N,int*a){i(n,r(gC.bi=vLit(ai),max_var=mx(max_var,r/2);hp_put(r)));R clause(n,gC.b);}
// TODO: minimization
// TODO: resets
V back_to(I lv){if(lv>=gLv.n)R;I i;for(i=gQ.n-1;i>=gLv.a[lv];i--)
 {I v=gQ.ai;v(clr,a);v(clr,v);hp_put(v);}gQ.n=gQ.head=i+1; gLv.n=lv;}
Lit branch(V){Lit v;do{if(gH.n==0)R 0;v=hp_pop();}W(v(get,a));R v|rng()<_/2;}
V vbump(I i){gV.ai++;if(gH.bi)hp_up(gH.bi-1);}V vdecay(V){i(max_var,gV.ai*=0.998f);}
V simplify(V){AS(gLv.n==0);if(simp.props>0||simp.qn==gQ.n)R;
 // k(gC.given,gC.n,I cr=k;if(j(cn,if(val(ca[j]))B))unclause(cr);
 //  else gC.a[k++]=cc;);simp.qn=gQ.n;simp.props=gC.n+gC.end-gC.temp;
}
I prop(V){W(gQ.head<gQ.n){
 Lit v=deq();if(!wv.a)continue; Watcher*i,*j,*end=wv.a+wv.n;simp.props--;
 for(i=j=wv.a;i!=end;){if(i->c==_){i_;continue;}
  if(val(i->bl)){j_=i_;continue;}I cr=i->c;Lit*a=ca;
  if(*a==(v^1))swp(*a,a[1]);if(*a!=i_.bl&&val(*a)){j_.bl=*a;continue;}
  if(k(2,cn,if(!val(ak^1)){swp(a[1],ak);watch(cr,a[1],*a);B}))
   continue;j_.bl=*a;if(val(*a^1)){W(i!=end)j_=i_;wv.n-=i-j;R cr;}
  enq(*a,cr);}wv.n-=i-j;}R _;}
I analyze(I cr,I*lv){N=1;Lit*a=gC.b;I deps=0,i=gQ.n;Lit v=0;
 do{AS(cr!=_);AS(!v||v==*ca);
  k(!!v,cn,Lit v=ca[k];if(!v(get,sn)&&gV.lv[v/2]){vbump(v/2);v(set,sn);
   if(gV.lv[v/2]<gLv.n)a[n++]=v;else deps++;});
  W(v=gQ.a[--i],!v(get,sn));cr=gV.c[v/2];v(clr,sn);deps--;
 }W(deps>0);*a=v^1;i(n,gA.sn[ai/128]=0);if(n==1){*lv=0;R n;}
 i=1;k(2,n,if(gV.lv[ak/2]>gV.lv[ai/2])i=k);*lv=gV.lv[ai/2];swp(a[1],ai);R n;}
I solve(){init();i(attempts,I conf=prop();  P(i);P(conf);dump();
 if(conf!=_){pf("conflict!\n")if(gLv.n==0)R 0;I lv=0;N=analyze(conf,&lv);back_to(lv);
  I cr=clause(n,gC.b);if(n>1)enq(*gC.b,cr);vdecay();
 }else{if(gLv.n==0)simplify();
  Lit v=branch();if(!v)R 1;p(gLv,gQ.n)enq(v,_);}
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
