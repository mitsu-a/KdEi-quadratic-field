#include <utility>
#include <numeric>

// @return x mod m
long long MOD(long long x,long long m){
    x%=m;
    if(x<0)x+=m;
    return x;
}

// @return pair(x,y) s.t. ax+by=gcd(a,b)
std::pair<long long,long long> solve_lineareq(long long a,long long b){
    if(b==0)return {1,0};
    long long neb=MOD(a,b);
    auto [x,y]=solve_lineareq(b,neb);
    return {y,x-(a-neb)/b*y};
}

// @return x s.t. x=a1 mod m1 & x=a2 mod m2 & 0<=x<lcm(m1,m2).
long long garner(long long a1,long long m1,long long a2,long long m2){
    a1=MOD(a1,m1);
    a2=MOD(a2,m2);
    auto g=std::gcd(m1,m2);
    if(a1%g!=a2%g){
        return -1;
    }
    else{
        long long p=solve_lineareq(m1,m2).first;
        return MOD(a1+(a2-a1)/g*m1*p,m1/g*m2);
    }
}