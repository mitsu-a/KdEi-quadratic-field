#include <utility>

// @return pair(x,y) s.t. ax+by=gcd(a,b)
std::pair<int,int> solve_lineareq(int a,int b){
    if(b==0)return {1,0};
    int neb=a%b;
    if(neb<0)neb+=b;
    auto [x,y]=solve_lineareq(b,neb);
    return {y,x-(a-neb)/b*y};
}