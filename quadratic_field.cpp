#include<iostream>
#include<vector>
#include<queue>
#include<utility>
#include<assert.h>
#include<numeric>
#include<set>

#define MOD4(d) (d%4+4)%4

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
        int trace()const{
            return (*this+this->conjugate).a;
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
        elem& operator%=(const elem r){//mod(r) Θ(N(r))
            if(r==0)return *this;
            auto [x,y]=r.mod_representative();
            this->b%=y;
            this->a%=r.norm();

            for(int i=0;i<x;i++)for(int j=0;j<y;j++){
                if((*this-elem(i,j)).is_divided_by(r)){
                    this->a=i;
                    this->b=j;
                    return *this;
                }
            }
            assert(false);
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
        friend elem operator%(elem l,const elem r){//Θ(|N(r)|)
            return l%=r;
        }
        static elem add_id(){
            return {0,0};
        }
        static elem multi_id(){
            return {1,0};
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
        std::pair<int,int> mod_representative()const{//雪江整数2 命題1.10.7　[x,y]をreturnするとして， y√d==0 mod(*this) になるような取り方．
            if(a==0 && b==0)return std::make_pair(0,0);
            const int n=std::abs(norm());
            int x,y;
            if(MOD4(d)==1){
                x=a;
                y=(d-1)/4*b;
            }
            else{
                x=a;
                y=d*b;
            }
            int g=std::gcd(x,y);
            return std::make_pair(std::gcd(g,n),n/std::gcd(g,n));
        }
        bool mod_eq(elem l,elem r)const{//l==r mod(*this)
            return this->is_divisor_of(l-r);
        }
    };


    struct ideal{
        elem gen[2];
        ideal(){
            gen[0]=0;
            gen[1]=0;
        }
        ideal(std::vector<elem> vec){//O(|vec|*max(N(vec))^2) 程度．
            for(int i=0;i<std::min<int>(2,vec.size());i++)gen[i]=vec[i];
            int beg=2;
            if(gen[0]==0){
                if(gen[1]!=0)std::swap(gen[0],gen[1]);
                else{
                    for(;beg<(int)vec.size();beg++){
                        if(vec[beg]!=0)break;
                    }
                    if(beg==(int)vec.size())return;
                    std::swap(vec[beg],gen[0]);
                }
            }
            if(gen[0]==0)std::swap(gen[0],gen[1]);

            for(int i=beg;i<(int)vec.size();i++){
                //A/<gen[0]>において， <gen[1],vec[i]> は単項生成なはずなので，その生成元を求める．
                gen[1]%=gen[0];
                vec[i]%=gen[0];
                auto [l,r]=gen[0].mod_representative();
                auto make_next=[&](elem t)->std::vector<elem>{
                    return {(t+gen[1])%gen[0],(t+gen[1]*elem(0,1))%gen[0],(t+vec[i])%gen[0],(t+vec[i]*elem(0,1))%gen[0]};
                };
                std::vector<elem> values;
                bool seen[l][r]={};
                seen[0][0]=true;
                std::queue<elem> q;
                q.emplace(0);
                while(!q.empty()){
                    elem now=q.front();q.pop();
                    values.emplace_back(now);
                    for(elem ne:make_next(now))if(!seen[ne.a][ne.b]){
                        seen[ne.a][ne.b]=true;
                        q.emplace(ne);
                    }
                }
                for(elem val:values){
                    auto make_next_2=[&](elem t)->std::vector<elem>{
                        return {(t+val)%gen[0],(t+val*elem(0,1))%gen[0]};
                    };
                    for(int i=0;i<l;i++)for(int j=0;j<r;j++)seen[i][j]=false;
                    seen[0][0]=true;
                    std::queue<elem> q;
                    q.emplace(0);
                    int cnt=0;
                    while(!q.empty()){
                        elem now=q.front();q.pop();
                        cnt++;
                        for(elem ne:make_next_2(now))if(!seen[ne.a][ne.b]){
                            seen[ne.a][ne.b]=true;
                            q.emplace(ne);
                        }
                    }
                    if(cnt==(int)values.size()){
                        gen[1]=val;
                        break;
                    }
                }
            }
            return;
        }
        ideal operator+(const ideal &r)const{
            return ideal({gen[0],gen[1],r.gen[0],r.gen[1]});
        }
        ideal operator*(const ideal &r)const{
            return ideal({gen[0]*r.gen[0],gen[0]*r.gen[1],gen[1]*r.gen[0],gen[1]*r.gen[1]});
        }
        ideal operator/(const ideal &r)const{}//書く．
        bool contains(elem x)const{//O(N(gen[0])^2) 
            x%=this->gen[0];
            if(x==0)return true;
            elem val=gen[1]%gen[0];
            auto [l,r]=gen[0].mod_representative();
            //(A/I)/(J/I) ≅ A/J を使う．
            //x \in <val> (A/I において) を判定すればいい．
            auto make_next=[&](elem t)->std::vector<elem>{
                return {(t+val)%gen[0],(t+val*elem(0,1))%gen[0]};
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
        bool operator==(const ideal &r){//O(|N|^2)
            bool ok=true;
            ok&=this->contains(r.gen[0]);
            ok&=this->contains(r.gen[1]);
            ok&=r.contains(this->gen[0]);
            ok&=r.contains(this->gen[1]);
            return ok;
        }
        //単項イデアルのみ
        std::vector<ideal> prime_factorize(){//単項生成イデアルのみ． O(N^3)程度． アティマク演習
            assert(gen[1]==0);
            auto [x,y]=gen[0].mod_representative();
            bool al[x][y]={};
            al[0][0]=true;
            std::set<std::pair<int,int>> set;
            for(int i=0;i<x;i++)for(int j=0;j<y;j++){
                if(al[i][j])continue;
                else{
                    elem val=elem(i,j);
                    auto make_next=[&](elem t)->std::vector<elem>{
                        return {(t+val)%gen[0],(t+val*elem(0,1))%gen[0]};
                    };
                    int cnt=0;
                    std::vector<elem> to_erase;
                    bool seen[x][y]={};
                    seen[0][0]=true;
                    std::queue<elem> q;
                    q.emplace(0);
                    while(!q.empty()){//O(N^2) make_nextでO(N)かかるため．
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
            std::vector<ideal> res;
            res.reserve(set.size());
            for(auto t:set){
                res.push_back(ideal({elem(t.first,t.second),elem(gen[0].a,gen[0].b)}));
            }
            return res;
        }
    };
};

int main(){}
