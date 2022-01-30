#include <iostream>
#include <vector>
#include <set>
#include <cassert>
#include <atcoder/modint>
#include <random>
#include "basic_functions.hpp"


using mint=atcoder::modint;

using std::cout;
using std::vector;

std::mt19937_64 rnd;

//できているもの
//Zのイデアルのstrong Gröbner basisを求めるアルゴリズム

//作りたい（整数環計算に使うなら必要そうな）もの
//Z/nZでのstrong Gröbner basisを求めるアルゴリズム
//-> A/(a+b√d)の計算で代表元を求める際に、Z[x]/(a+bx,x^2-d)の計算をすれば良い　これは結局(Z/cZ)[x]/(a+bx) のような形になるので、その計算に使えるはず（特により高次の際）

//現状の実装の要件
//基本：PIDならなんでも良い %演算子などは必要
//gcdなどを使う場合：体　できれば有限体（誤差が怖い）

//改善案
//f(x)をf(x)=x^i * g(x)なる(i,g)の組として保持する（単項式の扱いが楽になる、単項式をかける操作は多いので実装も綺麗になって良いかもしれない）

//最高次の係数は(多項式が0の場合を除いて)非0になるようにする

//sizeをdegで書き換える
//R/nRにおける実装はのちほど

template <typename T>
struct polynomial_ring{
    struct elem : vector<T> {
        using vector<T>::vector;
        // @return degree of the polynomial.(-1 iff the polynomial is zero.)
        int deg()const{
            assert(this->size());
            if(this->size()==1 && (*this)[0]==0)return -1;
            return this->size()-1;
        }
        elem operator-()const{
            elem res(*this);
            for(T &v:res)v=-v;
            return res;
        }
        elem& operator+=(const elem r){
            if(this->size()<r.size())this->resize(r.size());
            size_t sz=1;
            for(size_t i=0;i<this->size();i++){
                (*this)[i]+=r[i];
                if(typeid(T)==typeid(double)){
                    if(std::abs((*this)[i])>1e-8)sz=i+1;
                }
                else if((*this)[i]!=0)sz=i+1;
            }
            this->resize(sz);
            return *this;
        }
        elem& operator-=(const elem r){
            if(this->size()<r.size())this->resize(r.size());
            size_t sz=1;
            for(size_t i=0;i<this->size();i++){
                (*this)[i]-=r[i];
                if(typeid(T)==typeid(double)){
                    if(std::abs((*this)[i])>1e-8)sz=i+1;
                }
                else if((*this)[i]!=0)sz=i+1;
            }
            this->resize(sz);
            return *this;
        }
        elem& operator*=(const T r){
            if(r==0){
                *this=elem({0});
                return *this;
            }
            for(T &v:*this)v*=r;
            return *this;
        }
        elem operator*(const T r)const{
            auto res=*this;
            return res*=r;
        }
        //愚直な積
        elem operator*(const elem &r)const{
            if(r.size()==1)return (*this)*(r[0]);
            else if(this->size()==1)return r*(*this)[0];
            elem res(this->deg()+r.deg()+1);
            for(int i=0;i<=this->deg();i++)for(int j=0;j<=r.deg();j++){
                res[i+j]+=(*this)[i]*r[j];
            }
            return res;
        }
        elem& operator*=(const elem &r){
            return *this=(*this)*r;
        }
        //仮定：fをgが割る
        elem operator/(const elem g)const{
            elem f=*this;
            elem res(f.deg()-g.deg()+1);
            while(f.deg()>=0){
                res[f.deg()-g.deg()]+=f.back()/g.back();
                f=f.top_reduction_by(g);
            }
            return res;
        }
        elem derivative()const{
            elem res(this->deg());
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
        //Zなどで運用する際は後半をつける
        bool top_reduces(const elem &r)const{
            return r.size()>=this->size();// && r.back()%this->back()==0;
        }
        elem top_reduction_by(const elem &r)const{
            elem res=*this;
            assert(r.top_reduces(res));
            const int dif=res.size()-r.size();
            assert(dif>=0);
            int sz=1;
            for(size_t i=0;i<r.size();i++){
                //res.back()が書き換わるのは最後なので、正しく計算できる
                res[i+dif]-=res.back()/r.back() * r[i];
                if(res[i+dif]!=0)sz=i+dif+1;
            }
            res.resize(sz);
            assert(res.size());
            return res;
        }
        elem& monicize(){
            *this*=1/this->back();
            return *this;
        }
        elem normal_form(const vector<elem> &G)const{
            elem res=*this;
            //while(res!=0)
            while(res.deg()!=-1){
                //1度でもreduceされたらtrueに
                bool reduced=false;
                for(const elem &g:G){
                    if(g.top_reduces(res)){
                        //top-reductionする
                        res=res.top_reduction_by(g);
                        reduced=true;
                    }
                }
                if(!reduced)break;
            }
            return res;
        }
        
        friend elem gpoly(const elem &l,const elem &r){
            //lc(l)x+lc(r)y=gcd(lc(l),lc(r))
            auto [x,y]=solve_lineareq(l.back(),r.back());
            elem res(std::max(l.size(),r.size()));
            for(size_t i=0;i<l.size();i++)res[res.size()-l.size()+i]+=l[i]*x;
            for(size_t i=0;i<r.size();i++)res[res.size()-r.size()+i]+=r[i]*y;
            return res;
        }
        friend elem spoly(const elem &f,const elem &g){
            T a=lcm(f.back(),g.back());
            T a_f=a/f.back(),a_g=a/g.back();
            elem res(std::max(f.size(),g.size()));
            for(size_t i=0;i<f.size();i++)res[res.size()-f.size()+i]+=f[i]*a_f;
            for(size_t i=0;i<g.size();i++)res[res.size()-g.size()+i]-=g[i]*a_g;
            size_t sz=1;
            for(size_t i=0;i<res.size();i++)if(res[i])sz=i+1;
            res.resize(sz);
            return res;
        }
    };
    struct ideal : vector<elem> {
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
                h=h.normal_form(G);
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
};

template<typename T>
using P=typename polynomial_ring<T>::elem;

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
            y=y.top_reduction_by(x);
        }
        swap(x,y);
    }
    return y;
}



//速くできる、はず　一旦妥協
template<typename T>
P<T> MOD(P<T> f,const P<T> &mod){
    assert(f.size());
    while(mod.top_reduces(f)){
        f=f.top_reduction_by(mod);
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
template<typename T>
vector<std::pair<P<T>,int>> square_free_decomposition(P<T> f){
    vector<std::pair<P<T>,int>> res;
    P<T> flat=f/gcd_of_poly<T>(f,f.derivative());
    int m=0;
    while(flat.deg()>0){
        print_poly<T>(f);
        print_poly<T>(flat);
        cout << "waaaaa ";
        print_poly<T>(MOD<T>(f,flat));
        while(MOD<T>(f,flat).deg()==-1){
            cout << "D\n";
            f=f/flat;
            m++;
        }
        P<T> flat1=gcd_of_poly<T>(f,flat);
        cout << "flat1 ";
        print_poly<T>(flat1);
        P<T> g=flat/flat1;
        flat=flat1;
        res.emplace_back(g,m);
    }
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
        g=MODPOW<T>(g,t,f);
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


int main(){
    mint::set_mod(10007);
    std::random_device seed;
    rnd.seed(seed());
/*-------------------------------------------------*/

    int a;
    std::cin >> a;
    using Fpx=polynomial_ring<mint>;
    Fpx::elem f({mint(a),1}),ff({mint(a),0,1});//x+a
    f=f*f*f*ff*ff*ff*ff;
    print_poly<mint>(f);
    auto res=square_free_decomposition<mint>(f);
    for(auto [g,m]:res){
        g.monicize();
        cout << m << ' ';
        print_poly<mint>(g);
    }
    
    Fpx::elem g({27});
    Fpx::elem h({1,3336});
    print_poly<mint>(gcd_of_poly<mint>(g,h));
}