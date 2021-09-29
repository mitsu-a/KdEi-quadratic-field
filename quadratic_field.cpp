#include <iostream>
#include <vector>
#include <queue>
#include <utility>
#include <assert.h>
#include <numeric>
#include <set>
#include "basic_functions.hpp"

#define MOD4(d) (d%4+4)%4

//d:平方因子を持たず，0でも1でもない整数
//Remainder関数（命題3.1.6）：112行目

//その他の関数
// a.conjugate():aの共役元を返す
// a.norm():aのノルムを返す
template<int &d>
struct ring_of_integer{
    struct elem{
        int a,b;
        elem():a(0),b(0){}
        elem(const int _a):a(_a),b(0){}
        elem(const int _a,const int _b):a(_a),b(_b){}
        elem operator-()const{
            return {-a,-b};
        }
        elem conjugate()const{
            return (MOD4(d)==1 ? elem(a+b,-b):elem(a,-b));
        }
        int norm()const{
            return (*this * this->conjugate()).a;
        }
        friend bool operator==(const elem l,const elem r){
            return l.a==r.a && l.b==r.b;
        }
        friend bool operator!=(const elem l,const elem r){
            return !(l==r);
        }
        elem& operator+=(const elem r){
            this->a+=r.a;
            this->b+=r.b;
            return *this;
        }
        elem& operator-=(const elem r){
            this->a-=r.a;
            this->b-=r.b;
            return *this;
        }
        elem& operator*=(const elem r){
            if(MOD4(d)==1){
                int old_a=this->a;
                this->a=this->a*r.a + this->b*r.b*(d-1)/4;
                this->b=this->b*r.b + this->b*r.a + old_a*r.b;
            }
            else{
                int old_a=this->a;
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
            else if(r.a==0)os << r.b << (MOD4(d)==1 ? "\\frac{1+\\sqrt{":"\\sqrt{") << d << (MOD4(d)==1 ? "}}{2}":"}");
            else if(r.b==0)os << r.a;
            else os << r.a << (r.b>0 ? "+":"") << r.b << (MOD4(d)==1 ? "\\frac{1+\\sqrt{":"\\sqrt{") << d << (MOD4(d)==1 ? "}}{2}":"}");
            return os;
        }
        bool is_divided_by(const elem r)const{
            assert(r!=0);
            elem prod=*this * r.conjugate();
            int div=r.norm();
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
        // @return pair(u,v) s.t. {elem(x,y) | 0<=x<u, 0<=y<v} is a complete system of representatives in A/(*this).
        std::pair<int,int> mod_representative()const{
            assert((*this)!=0);
            const int n=std::abs(norm());
            int g;
            if(MOD4(d)==1){
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
            const int s=r.a, t=r.b, n=std::abs(r.norm());//r=s+t\alpha
            int a=val.a, b=val.b;//x=a+b\alpha
            a%=n;if(a<0)a+=n;
            b%=v;if(b<0)b+=v;

            const int X=a/u*u;
            int Y_dt,Y_s,mod_dt,mod_s,g_dt,g_s;
            //solve (td/gcd(td,N(r)))Y \equiv Xs/gcd(td,N(r)) or (tD / gcd(tD,N(r)))Y \equiv -X(s+t)/gcd(tD,N(r)) (D=(1-d)/4)
            {
                const int D=(1-d)/4;
                int u,v;
                if(MOD4(d)==1){
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
                const int u_inv=solve_lineareq(u,mod_dt).first%mod_dt;
                Y_dt=v*u_inv%mod_dt;
                if(Y_dt<0)Y_dt+=mod_dt;
            }
            //solve (s/gcd(s,N(r)))Y \equiv Xt/gcd(s,N(r))
            {
                g_s=std::gcd(s,n);
                mod_s=n/g_s;
                const int u=s/g_s%mod_s, v=t*X/g_s%mod_s;
                //solve uY=v mod(mod_s)
                const int u_inv=solve_lineareq(u,mod_s).first%mod_s;
                Y_s=v*u_inv%mod_s;
                if(Y_s<0)Y_s+=mod_s;
            }

            //Y mod(lcm(mod_dt,mod_s)) i.e. mod(v)
            int Y=garner(Y_dt,mod_dt,Y_s,mod_s);

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
        ideal(std::vector<elem> vec){//O((N(e)^2+N(e)*|vec|)*log(max(e.a,e.b,e.N))) 程度． (e:vecの元のうちノルム最小の元)
            gen[0]=gen[1]=0;
            for(elem val:vec)if(val!=0)gen[0]=val;
            if(gen[0]==0)return;
            for(elem val:vec)if(val!=0 && std::abs(val.norm())<std::abs(gen[0].norm()))gen[0]=val;

            auto [x,y]=gen[0].mod_representative();

            //幅優先探索：O(N(gen[0])*|vec|*log(max(a,b,N)))
            int cnt=0;
            std::queue<elem> q;
            q.emplace(0);
            bool seen[x][y]={};
            seen[0][0]=true;
            //sを用いた遷移：+s,-s,+s√d,-s√d
            while(!q.empty()){
                cnt++;
                elem now=q.front();q.pop();
                for(elem edge:vec){
                    elem ne[]={now+edge,now-edge,now+edge*elem(0,1),now-edge*elem(0,1)};
                    for(int i=0;i<4;i++){
                        ne[i]=Remainder(ne[i],gen[0]);
                        if(!seen[ne[i].a][ne[i].b]){
                            seen[ne[i].a][ne[i].b]=true;
                            q.emplace(ne[i]);
                        }
                    }
                }
            }

            //O(N(gen[0])^2*log(max(a,b,N)))
            for(int i=0;i<x;i++)for(int j=0;j<y;j++)if(seen[i][j]){
                elem val(i,j);
                int val_cnt=0;
                const elem edge[]={val,-val,val*elem(0,1),-val*elem(0,1)};

                //幅優先探索 O(N(gen[0])*log(max(a,b,N)))
                bool al[x][y]={};
                al[0][0]=true;
                q.emplace(0);
                while(!q.empty()){
                    val_cnt++;
                    elem now=q.front();q.pop();
                    for(int k=0;k<4;k++){
                        elem ne=now+edge[k];
                        ne=Remainder(ne,gen[0]);
                        if(!al[ne.a][ne.b]){
                            al[ne.a][ne.b]=true;
                            q.emplace(ne);
                        }
                    }
                }
                if(cnt==val_cnt){
                    gen[1]=val;
                    return;
                }
            }
            assert(false);
            return;
        }
        ideal operator+(const ideal &r)const{
            return ideal({gen[0],gen[1],r.gen[0],r.gen[1]});
        }
        ideal operator*(const ideal &r)const{
            return ideal({gen[0]*r.gen[0],gen[0]*r.gen[1],gen[1]*r.gen[0],gen[1]*r.gen[1]});
        }
        ideal operator/(const ideal &r)const{}//書く．
        bool contains(elem x)const{//O(Nlog(max(a,b,N)))程度．ただし a,b,N は全て gen[0] のもの．
            x=Remainder(x,this->gen[0]);
            if(x==0)return true;
            elem val=Remainder(gen[1],gen[0]);
            auto [l,r]=gen[0].mod_representative();
            //(A/I)/(J/I) ≅ A/J を使う．
            //x \in <val> (A/I において) を判定すればいい．
            auto make_next=[&](elem t)->std::vector<elem>{
                return {Remainder(t+val,gen[0]),Remainder(t+val*elem(0,1),gen[0])};
            };
            bool seen[l][r]={};
            seen[0][0]=true;
            std::queue<elem> q;
            q.emplace(0);
            while(!q.empty()){
                elem now=q.front();q.pop();
                for(elem ne:make_next(now))if(!seen[ne.a][ne.b]){
                    if(ne==x)return true;
                    seen[ne.a][ne.b]=true;
                    q.emplace(ne);
                }
            }
            return false;
        }
        bool operator==(const ideal &r){//O(Nlog(max(a,b,N)))．ただし各イデアルの gen[0] のもの．
            bool ok=true;
            ok&=this->contains(r.gen[0]);
            ok&=this->contains(r.gen[1]);
            ok&=r.contains(this->gen[0]);
            ok&=r.contains(this->gen[1]);
            return ok;
        }
        // @return the vector of pairs(p,i) s.t. (*this) is a product of p^i.
        std::vector<std::pair<ideal,int>> prime_factorize(){//単項生成イデアルのみ． アティマク演習．
            auto [x,y]=gen[0].mod_representative();
            bool al[x][y]={};
            al[0][0]=true;
            std::set<std::pair<int,int>> set;
            for(int i=0;i<x;i++)for(int j=0;j<y;j++){
                if(al[i][j])continue;
                else{
                    elem val=elem(i,j);
                    auto make_next=[&](elem t)->std::vector<elem>{
                        return {Remainder(t+val,gen[0]),Remainder(t+val*elem(0,1),gen[0])};
                    };
                    int cnt=0;
                    std::vector<elem> to_erase;
                    bool seen[x][y]={};
                    seen[0][0]=true;
                    std::queue<elem> q;
                    q.emplace(0);
                    while(!q.empty()){//O(N)
                        auto now=q.front();q.pop();
                        to_erase.emplace_back(now);
                        cnt++;
                        for(elem ne:make_next(now))if(!seen[ne.a][ne.b]){
                            seen[ne.a][ne.b]=true;
                            q.emplace(ne);
                        }
                    }
                    if(cnt==std::abs(gen[0].norm()))continue;
                    for(elem t:to_erase){//O(NlogN)
                        set.erase({t.a,t.b});
                        al[t.a][t.b]=true;
                    }
                    set.emplace(i,j);
                }
            }
            std::vector<std::pair<ideal,int>> res;
            res.reserve(set.size());
            for(auto t:set){
                int cnt=-1;
                ideal J({1});
                while(J.contains(gen[0]) && J.contains(gen[1])){
                    J=J*ideal({gen[0],elem(t.first,t.second)});
                    cnt++;
                }
                if(cnt)res.push_back({ideal({elem(t.first,t.second),gen[0]}),cnt});
            }
            return res;
        }
    };
};

int main(){}