#ifndef POLYNOMIAL
#define POLYNOMIAL

#include <iostream>
#include <vector>
#include <set>
#include <cassert>
#include <atcoder/modint>
#include <random>
#include "basic_functions.hpp"

//使う時、必ず polynomial::init(mod) を実行する

namespace polynomial_sp{

using mint=atcoder::modint;
using std::cout;
using std::vector;

std::mt19937_64 rnd;

void init(const int mod=0){
    if(mod){
        mint::set_mod(mod);
    }
    std::random_device seed_gen;
    rnd.seed(seed_gen());
    return;
}

//できているもの
//Zのイデアルのstrong Gröbner basisを求めるアルゴリズム

//現状の実装の要件
//基本：PIDならなんでも良い %演算子などは必要
//gcdなどを使う場合：体　できれば有限体（誤差が怖い）

//改善案
//f(x)をf(x)=x^i * g(x)なる(i,g)の組として保持する（単項式の扱いが楽になる、単項式をかける操作は多いので実装も綺麗になって良いかもしれない）

template <typename T>
struct polynomial : vector<T> {
    using vector<T>::vector;
    // @return degree of the polynomial.(-1 iff the polynomial is zero.)
    int deg()const{
        assert(this->size());
        if(this->size()==1 && (*this)[0]==0)return -1;
        return this->size()-1;
    }
    polynomial operator-()const{
        polynomial res(*this);
        for(T &v:res)v=-v;
        return res;
    }
    polynomial& operator+=(const polynomial r){
        if(this->size()<r.size())this->resize(r.size());
        size_t sz=1;
        for(size_t i=0;i<this->size();i++){
            (*this)[i]+=r[i];
            if((*this)[i]!=0)sz=i+1;
        }
        this->resize(sz);
        return *this;
    }
    polynomial& operator-=(const polynomial r){
        if(this->size()<r.size())this->resize(r.size());
        size_t sz=1;
        for(size_t i=0;i<this->size();i++){
            (*this)[i]-=r[i];
            if((*this)[i]!=0)sz=i+1;
        }
        this->resize(sz);
        return *this;
    }
    polynomial operator-(const polynomial r){
        auto res=*this;
        return res-=r;
    }
    polynomial& operator*=(const T r){
        if(r==0){
            *this=polynomial({0});
            return *this;
        }
        for(T &v:*this)v*=r;
        return *this;
    }
    polynomial operator*(const T r)const{
        auto res=*this;
        return res*=r;
    }
    //愚直な積
    polynomial operator*(const polynomial &r)const{
        if(r.size()==1)return (*this)*(r[0]);
        else if(this->size()==1)return r*(*this)[0];
        polynomial res(this->deg()+r.deg()+1);
        for(int i=0;i<=this->deg();i++)for(int j=0;j<=r.deg();j++){
            res[i+j]+=(*this)[i]*r[j];
        }
        return res;
    }
    polynomial& operator*=(const polynomial &r){
        return *this=(*this)*r;
    }
    //仮定：fをgが割る
    polynomial operator/(const polynomial g)const{
        polynomial f=*this;
        polynomial res(f.deg()-g.deg()+1);
        while(f.deg()>=0){
            res[f.deg()-g.deg()]+=f.back()/g.back();
            f=top_reduction_by(f,g);
        }
        return res;
    }
    polynomial derivative()const{
        polynomial res(this->deg());
        int sz=1;
        for(int i=1;i<=this->deg();i++){
            res[i-1]=i*(*this)[i];
            if(res[i-1]!=0){
                sz=i;
            }
        }
        res.resize(sz);
        return res;
    }
    polynomial& monicize(){
        *this*=1/this->back();
        return *this;
    }
};

template<typename T>
using P=polynomial<T>;

// @return true iff the first element top_reduces the second one.
template<typename T>
bool top_reduces(const P<T> &l,const P<T> &r){
    return r.deg()>=l.deg();
}
// @return true iff the first element top_reduces the second one.
bool top_reduces(const P<long long> &l,const P<long long> &r){
    return r.deg()>=l.deg() && r.back()%l.back()==0;
}

// @return the first element's top_reduction by the second one.
template<typename T>
P<T> top_reduction_by(P<T> l,const P<T> &r){
    assert(top_reduces(r,l));
    const int dif=l.size()-r.size();
    assert(dif>=0);
    int sz=1;
    for(size_t i=0;i<r.size();i++){
        //res.back()が書き換わるのは最後なので、正しく計算できる
        l[i+dif]-=l.back()/r.back() * r[i];
        if(l[i+dif]!=0)sz=i+dif+1;
    }
    l.resize(sz);
    assert(l.size());
    return l;
}

template<typename T>
P<T> normal_form(P<T> l,const vector<P<T>> &G){
    //while(l!=0)
    while(l.deg()!=-1){
        //1度でもreduceされたらtrueに
        bool reduced=false;
        for(const P<T> &g:G){
            if(top_reduces(g,l)){
                //top-reductionする
                l=top_reduction_by(l,g);
                reduced=true;
            }
        }
        if(!reduced)break;
    }
    return l;
}

template<typename T>
P<T> gpoly(const P<T> &l,const P<T> &r){
    //lc(l)x+lc(r)y=gcd(lc(l),lc(r))
    auto [x,y]=solve_lineareq(l.back(),r.back());
    P<T> res(std::max(l.size(),r.size()));
    for(size_t i=0;i<l.size();i++)res[res.size()-l.size()+i]+=l[i]*x;
    for(size_t i=0;i<r.size();i++)res[res.size()-r.size()+i]+=r[i]*y;
    return res;
}
template<typename T>
P<T> spoly(const P<T> &f,const P<T> &g){
    T a=std::lcm(f.back(),g.back());
    T a_f=a/f.back(),a_g=a/g.back();
    P<T> res(std::max(f.size(),g.size()));
    for(size_t i=0;i<f.size();i++)res[res.size()-f.size()+i]+=f[i]*a_f;
    for(size_t i=0;i<g.size();i++)res[res.size()-g.size()+i]-=g[i]*a_g;
    size_t sz=1;
    for(size_t i=0;i<res.size();i++)if(res[i])sz=i+1;
    res.resize(sz);
    return res;
}

template<typename T>
struct ideal : vector<polynomial<T>> {
    using elem=polynomial<T>;
    using vector<elem>::vector;
    ideal strong_grobner_basis()const{
        ideal G=*this;
        //いま、整域なのでapolyは全て0。よって考慮に入れなくて良い。
        //spolyはほぼtop-reductionになるが考慮対象にすべきなのか？
        std::set<elem> P;
        for(size_t i=0;i<this->size();i++)for(size_t j=0;j<i;j++){
            P.emplace(spoly((*this)[i],(*this)[j])); 
            P.emplace(gpoly((*this)[i],(*this)[j]));
        }
        P.erase(elem{0});
        while(!P.empty()){
            elem h=*P.begin();P.erase(P.begin());
            h=normal_form(h,G);
            if(h.size()>1ul || h[0]!=0){
                for(elem &g:G){
                    P.emplace(spoly(g,h));
                    P.emplace(gpoly(g,h));
                }
                G.emplace_back(h);
                P.erase(elem{0});
            }
        }
        return G;
    }
};


template<typename T>
void print_poly(P<T> x){
    if(x.deg()==-1){
        std::cout << "0\n";
        return;
    }
    for(int i=0;i<=x.deg();i++){
        std::cout << x[i] << "x^" << i;
        if(i==x.deg())cout << '\n';
        else cout << '+';
    }
}

//遅いもので妥協している　高速化はできるのでする（必要箇所が実装でき次第やる）
template<typename T>
P<T> gcd_of_poly(P<T> x,P<T> y){
    while(x.deg()!=-1){
        while(y.deg()>=x.deg()){
            y=top_reduction_by(y,x);
        }
        swap(x,y);
    }
    y.monicize();
    return y;
}

//速くできる、はず　一旦妥協
template<typename T>
P<T> MOD(P<T> f,const P<T> &mod){
    assert(f.size());
    while(top_reduces(mod,f)){
        f=top_reduction_by(f,mod);
        if(f.size()==0)f=P<T>({0});
    }
    assert(f.size());
    while(f.size()>1 && f.back()==0)f.pop_back();
    if(f.size()==0)f=P<T>({0});
    return f;
}

template<typename T>
P<T> MODPOW(P<T> f,long long n,const P<T> &mod){
    P<T> res({1});
    while(n){
        if(n&1)res=MOD<T>(res*f,mod);
        f=MOD<T>(f*f,mod);
        n/=2;
    }
    return res;
}

//6.2節
//(g,i)：g^i
//標数p
template<typename T>
vector<std::pair<P<T>,int>> square_free_decomposition(P<T> f,int p){
    vector<std::pair<P<T>,int>> res;
    if(f.derivative().deg()!=-1){
        P<T> flat=f/gcd_of_poly<T>(f,f.derivative());
        int m=0;
        while(flat.deg()>0){
            while(MOD<T>(f,flat).deg()==-1){
                f=f/flat;
                m++;
            }
            P<T> flat1=gcd_of_poly<T>(f,flat);
            P<T> g=flat/flat1;
            flat=flat1;
            res.emplace_back(g,m);
        }
    }
    ///////////////////////////////////////////////////////////////改善の余地あり
    if(f.deg()>1){
        std::uniform_int_distribution<int> val(0,p);
        P<T> g(f.deg()/p+1);
        while(true){
            for(int i=0;i<=g.deg();i++){
                g[i]=val(rnd);
            }
            if(MODPOW<T>(g,p,f).deg()==-1){
                f=g;
                break;
            }
        }
        auto vec=square_free_decomposition(f,p);
        for(auto [f,i]:vec)res.emplace_back(f,i*p);
    }
    return res;
}

//6.5節 distinct degree factorization
//f：無平方な多項式
//(f_i,i)：i次の既約多項式
//標数p
template<typename T>
vector<std::pair<P<T>,int>> distinct_degree_factorization(P<T> f,const int p){
    vector<std::pair<P<T>,int>> res;
    P<T> w({0,1}),x({0,1});//x
    for(int i=1;2*i<=f.deg();i++){
        w=MODPOW<T>(w,p,f);//x^(p^i)
        P<T> g=gcd_of_poly<T>(f,w-x);//x^(p^i)-x
        if(g.deg()>0){
            res.emplace_back(g,i);
            f=f/g;
            w=MOD<T>(w,f);
        }
    }
    if(f.deg()>0)res.emplace_back(f,f.deg());
    return res;
}

//Cantor-Zassenhaus　ただし改善版の6.6節
//f：無平方、相異なるd_max次の既約多項式の積
//標数p
//適切に動作するにはp^d_maxが64bit整数に収まることが必要
template<typename T>
vector<P<T>> CZ_factorize(P<T> f,const int d_max,const int p){
    if(f.deg()==d_max)return {f};
    std::uniform_int_distribution<int> deg(1,2*d_max-1),value(0,p-1);
    const long long t=(mypow(p,d_max)-1)/2;
    int cnt=1000;
    while(cnt--){
        const int d=deg(rnd);
        P<T> g(d+1);
        g.back()=1;
        for(int i=0;i<g.deg();i++)g[i]=value(rnd);
        if(p==2){
            P<T> G({0});
            for(int j=0;j<f.deg();j++){
                G+=g;
                G=MOD<T>(G,f);
                g*=g;
                g=MOD<T>(g,f);
            }
            g=G;
        }
        else g=MODPOW<T>(g,t,f);
        g[0]-=1;
        g=gcd_of_poly<T>(f,g);
        if(g.deg()>0 && g.deg()<f.deg()){
            auto res1=CZ_factorize<T>(g,d,p),res2=CZ_factorize<T>(f/g,d,p);
            for(auto h:res2)res1.push_back(h);
            return res1;
        }
    }
    assert(false);
}

//標数p
//p^(結果に現れる最大次数)がオーバーフローしない必要がある
template<typename T>
vector<std::pair<P<T>,int>> factorize(P<T> f,const int p){
    auto sqf=square_free_decomposition<T>(f,p);
    vector<std::pair<P<T>,int>> res;
    for(auto [f,i]:sqf){
        for(auto [g,d]:distinct_degree_factorization<T>(f,p)){
            for(auto &h:CZ_factorize<T>(g,d,p)){
                res.emplace_back(h,i);
            }
        }
    }
    return res;
}

} // namespace polynomial

#endif // POLYNOMIAL