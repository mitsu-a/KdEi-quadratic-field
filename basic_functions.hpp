#ifndef BASIC_FUNCTIONS
#define BASIC_FUNCTIONS

#include <utility>
#include <numeric>
#include <atcoder/modint>

// @return x mod m
long long MOD(long long x,long long m){
    x%=m;
    if(x<0)x+=m;
    return x;
}

//オーバーフローに気をつける
long long mypow(const long long a,const long long b){
    if(b==1)return a;
    auto r=mypow(a,b/2);
    r*=r;
    if(b%2==1)r*=a;
    return r;
}

// @return pair(x,y) s.t. ax+by=|gcd(a,b)|
std::pair<long long,long long> solve_lineareq(long long a,long long b){
    if(b==0)return {(a>0 ? 1:-1),0};
    long long neb=a%b;
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

std::vector<std::pair<long long,int>> prime_factorize(long long x){
    std::vector<std::pair<long long,int>> res;
    for(long long i=2;i*i<=x;i++){
        int cnt=0;
        while(x%i==0){
            cnt++;
            x/=i;
        }
        if(cnt)res.emplace_back(i,cnt);
    }
    if(x!=1)res.emplace_back(x,1);
    return res;
}

template<int m>
std::ostream& operator<<(std::ostream &os,const atcoder::static_modint<m> v){
    os << v.val();
    return os;
}
template<int id>
std::ostream& operator<<(std::ostream &os,const atcoder::dynamic_modint<id> v){
    os << v.val();
    return os;
}

#endif // BASIC_FUNCTIONS