#include <iostream>
#include <vector>
#include <queue>
#include <utility>
#include <assert.h>
#include <numeric>
#include <set>
#include <map>
#include "basic_functions.hpp"
#include "polynomial.hpp"

//d:平方因子を持たず，0でも1でもなく，かつd≡2,3(mod4)を満たす整数．

template<long long &d,typename T=long long>
struct ring_of_integer{
    //a+b√d
    struct elem{
        T a,b;
        elem():a(0),b(0){}
        elem(const T _a):a(_a),b(0){}
        elem(const T _a,const T _b):a(_a),b(_b){}
        elem operator-()const{
            return {-a,-b};
        }
        elem conjugate()const{
            return (MOD(d,4)==1 ? elem(a+b,-b):elem(a,-b));
        }
        T norm()const{
            return (*this * this->conjugate()).a;
        }
        friend bool operator==(const elem l,const elem r){
            return l.a==r.a && l.b==r.b;
        }
        friend bool operator!=(const elem l,const elem r){
            return !(l==r);
        }
        elem& operator+=(const elem r){
            a+=r.a;
            b+=r.b;
            return *this;
        }
        elem& operator-=(const elem r){
            this->a-=r.a;
            this->b-=r.b;
            return *this;
        }
        elem& operator*=(const elem r){
            if(MOD(d,4)==1){
                T old_a=this->a;
                this->a=this->a*r.a + this->b*r.b*(d-1)/4;
                this->b=this->b*r.b + this->b*r.a + old_a*r.b;
            }
            else{
                T old_a=this->a;
                this->a = this->a*r.a + this->b*r.b*d;
                this->b = old_a*r.b + this->b*r.a;
            }
            return *this;
        }
        friend elem operator+(elem l,const elem r){
            return l+=r;
        }
        friend elem operator-(elem l,const elem r){
            return l-=r;
        }
        friend elem operator*(elem l,const elem r){
            return l*=r;
        }
        friend std::ostream& operator<<(std::ostream &os,const elem r){
            if(r.a==0 && r.b==0)os << 0;
            else if(r.a==0)os << r.b << (MOD(d,4)==1 ? "\\frac{1+\\sqrt{":"\\sqrt{") << d << (MOD(d,4)==1 ? "}}{2}":"}");
            else if(r.b==0)os << r.a;
            else os << r.a << (r.b>0 ? "+":"") << r.b << (MOD(d,4)==1 ? "\\frac{1+\\sqrt{":"\\sqrt{") << d << (MOD(d,4)==1 ? "}}{2}":"}");
            return os;
        }
        bool is_divided_by(const elem r)const{
            assert(r!=0);
            elem prod=*this * r.conjugate();
            T div=r.norm();
            return prod.a%div==0 && prod.b%div==0;
        }
        bool is_divisor_of(const elem r)const{
            return r.is_divided_by(*this);
        }
        bool is_unit()const{
            return std::abs(this->norm())==1;
        }
        bool is_integer()const{
            return b==0;
        }
        friend void swap(elem &l,elem &r){
            const elem x=r;
            r=l;
            l=x;
            return;
        }
        // @return pair(u,v) s.t. {elem(x,y) | 0<=x<u, 0<=y<v} is a complete system of representatives in A/(*this).
        std::pair<T,T> mod_representative()const{
            assert((*this)!=0);
            const T n=std::abs(norm());
            T g;
            if(MOD(d,4)==1){
                g=std::gcd(a,(d-1)/4*b);
            }
            else{
                g=std::gcd(a,d*b);
            }
            return std::make_pair(g,n/g);
        }
        // @return t s.t. t==val in A/(r)
        friend elem Remainder(const elem val,const elem r){
            assert(r!=0);
            //R={a+b\alpha | 0<=a<u,u<=b<v}
            const auto [u,v]=r.mod_representative();
            const T s=r.a, t=r.b, n=std::abs(r.norm());//r=s+t\alpha
            T a=val.a, b=val.b;//x=a+b\alpha
            a%=n;if(a<0)a+=n;
            b%=v;if(b<0)b+=v;

            const T X=a/u*u;
            T Y_dt,Y_s,mod_dt,mod_s,g_dt,g_s;
            //solve (td/gcd(td,N(r)))Y \equiv Xs/gcd(td,N(r)) or (tD / gcd(tD,N(r)))Y \equiv -X(s+t)/gcd(tD,N(r)) (D=(1-d)/4)
            {
                const T D=(1-d)/4;
                T u,v;
                if(MOD(d,4)==1){
                    g_dt=std::gcd(t*D,n);
                    mod_dt=n/g_dt;
                    u=t*D/g_dt%mod_dt, v=-(s+t)*X/g_dt%mod_dt;
                }
                else{
                    g_dt=std::gcd(t*d,n);
                    mod_dt=n/g_dt;
                    u=t*d/g_dt%mod_dt, v=s*X/g_dt%mod_dt;
                }
                //solve uY=v mod(mod_dt)
                const T u_inv=solve_lineareq(u,mod_dt).first%mod_dt;
                Y_dt=v*u_inv%mod_dt;
                if(Y_dt<0)Y_dt+=mod_dt;
            }
            //solve (s/gcd(s,N(r)))Y \equiv Xt/gcd(s,N(r))
            {
                g_s=std::gcd(s,n);
                mod_s=n/g_s;
                const T u=s/g_s%mod_s, v=t*X/g_s%mod_s;
                //solve uY=v mod(mod_s)
                const T u_inv=solve_lineareq(u,mod_s).first%mod_s;
                Y_s=v*u_inv%mod_s;
                if(Y_s<0)Y_s+=mod_s;
            }

            //Y mod(lcm(mod_dt,mod_s)) i.e. mod(v)
            T Y=garner(Y_dt,mod_dt,Y_s,mod_s);

            //X+Y√d=0 mod(r)
            a-=X,b-=Y;
            if(b<0)b+=v;
            return elem(a,b);
        }
    };

    struct ideal{
        elem gen[2];
        ideal(){
            gen[0]=0;
            gen[1]=0;
        }

        //方針：生成系の係数のgcdを分離して，残った部分のグレブナー基底から計算
        ideal(std::vector<elem> F){
            if(F.size()<=2){
                for(int i=0;i<int(F.size());i++)gen[i]=F[i];
                return;
            }
            int g=0;
            for(auto e:F)g=std::gcd(g,e.a),g=std::gcd(g,e.b);
            polynomial_sp::ideal<T> I(1);
            I.reserve(F.size()+1);
            I[0]={-d,0,1};
            for(auto e:F){
                I.push_back({e.a/g, e.b/g});
            }
            auto [a,b]=I.strong_grobner_basis_qf();
            a[0]%=b[0],a[1]%=b[0];
            gen[0]=elem(a[0],a[1])*g;
            gen[1]=b[0]*g;
            return;
        }
        ideal operator+(const ideal &r)const{
            return ideal({gen[0],gen[1],r.gen[0],r.gen[1]});
        }
        ideal operator*(const ideal &r)const{
            return ideal({gen[0]*r.gen[0],gen[0]*r.gen[1],gen[1]*r.gen[0],gen[1]*r.gen[1]});
        }
        bool Contains(elem x){
            if(gen[0]==0 && gen[1]==0)return x==0;
            const int gcd=std::gcd(std::gcd(gen[0].a, gen[0].b), std::gcd(gen[1].a, gen[1].b));
            if(!x.is_divided_by(gcd))return false;
            x.a/=gcd,x.b/=gcd;
            polynomial_sp::polynomial<T> f({-d,0,1}),g({gen[0].a/gcd,gen[0].b/gcd}),h({gen[1].a/gcd,gen[1].b/gcd}), X({x.a,x.b});
            polynomial_sp::ideal<T> I({f,g,h});
            auto [l,r]=I.strong_grobner_basis_qf();//Z[√d]のみ．
            return X.eval(-l[0])%r[0]==0;
        }
        bool Contains(ideal J){
            return Contains(J.gen[0]) && Contains(J.gen[1]);
        }
        bool operator==(ideal &r){
            return this->Contains(r) && r.Contains(*this);
        }
        // @return the vector of pairs(p,i) s.t. (*this) is a product of p^i.
        std::vector<std::pair<ideal,int>> PrimeFactorize()const{
            std::vector<std::pair<ideal,int>> res;
            assert(gen[0]!=0 || gen[1]!=0);
            long long g=std::gcd(std::gcd(gen[0].a,gen[0].b),std::gcd(gen[1].a,gen[1].b));

            for(auto [p,i]:prime_factorize(g)){
                polynomial_sp::init(p);
                auto fac=polynomial_sp::factorize(polynomial_sp::polynomial<polynomial_sp::mint>({-d,0,1}),p);

                //相対次数f=2
                if(fac.size()==1 && fac[0].second==1){
                    res.emplace_back(ideal({elem(p)}),i);
                }
                //相対次数f=1
                else{
                    for(auto [poly,j]:fac)res.emplace_back(ideal({elem(p),elem(poly[0].val(),poly[1].val())}),i*j);
                }
            }

            polynomial_sp::ideal<T> I({{-d,0,1},{gen[0].a/g,gen[0].b/g},{gen[1].a/g,gen[1].b/g}});
            auto [x,y]=I.strong_grobner_basis_qf();
            long long n=std::abs(y[0]);
            long long c(x[0]);
            for(auto [p,i]:prime_factorize(n)){
                ideal I({elem(p),elem(c,1)});
                for(auto &&[J,j]:res)if(I==J)j+=i,i=0;
                if(i)res.emplace_back(I,i);
            }
            return res;
        }
    };
};

bool is_PrimeNumber(int p){
    for(int i=2;i*i<=p;i++){
        if(p%i==0)return false;
    }
    return true;
}

long long d=7;

int main(){
    using A=ring_of_integer<d>;
    std::vector<int> PrimeIdeal(1001,-1);
    /*
    PrimeIdeal[i]=
     - iが素数でない：-1                    ->' 'を出力
     - iが素数であるが素イデアルを生成しない：0 ->'.'を出力
     - iが素数であり素イデアルを生成する：1    ->'#'を出力
    */
    for(int i=2;i<=1000;i++){
        if(is_PrimeNumber(i)){
            A::ideal I({i});
            auto v=I.PrimeFactorize();
            if(v.size()==1 && v.front().second==1){
                PrimeIdeal[i]=1;
            }
            else{
                PrimeIdeal[i]=0;
            }
        }
    }

    int m;
    std::cin >> m;
    for(int i=0;i<=1000;i++){
        char c=' ';
        if(PrimeIdeal[i]==0)c='.';
        else if(PrimeIdeal[i]==1)c='#';
        std::cout << c << " \n"[i%m==m-1];
    }
    std::cout << std::endl;
}

/*
i=0,1,...,1000について，次の操作を行う：
 - iが素数でない　　　　　　　　　　　　　　 : 空白文字を出力
 - iが素数だがZ[√7]で素イデアルを生成しない : 文字'.'を出力
 - iが素数で，Z[√7]で素イデアルを生成する　 : 文字'#'を出力
さらに，iがmの倍数になる毎に改行する（mは標準入力から与える）．

m=20を入力として与えると規則的な様子が観察される．
d,mの値を適当に変えることで様々な実験が可能（ただしdはmod4で2,3のいずれか，かつ平方因子を持ってはならない）．
*/