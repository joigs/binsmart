#include <vector>
#include <string>
#include <iostream>
#include <algorithm>
#include <limits>
#include <cstdint>
using namespace std;

enum class Base : uint8_t { S1D, S1D_PR, S1G, S1G_PR, S3D, S3D_PR, S3G, S3G_PR };

static inline string to_string_base(Base s){
    switch(s){
        case Base::S1D:    return "1D";
        case Base::S1D_PR: return "1D'";
        case Base::S1G:    return "1G";
        case Base::S1G_PR: return "1G'";
        case Base::S3D:    return "3D";
        case Base::S3D_PR: return "3D'";
        case Base::S3G:    return "3G";
        case Base::S3G_PR: return "3G'";
    } return "?";
}
static inline bool parse_state(string s, Base& out){
    for(char& c: s) c = (char)toupper((unsigned char)c);
    if(s=="1D")  { out=Base::S1D; return true; }
    if(s=="1D'") { out=Base::S1D_PR; return true; }
    if(s=="1G")  { out=Base::S1G; return true; }
    if(s=="1G'") { out=Base::S1G_PR; return true; }
    if(s=="3D")  { out=Base::S3D; return true; }
    if(s=="3D'") { out=Base::S3D_PR; return true; }
    if(s=="3G")  { out=Base::S3G; return true; }
    if(s=="3G'") { out=Base::S3G_PR; return true; }
    return false;
}

static inline int inverse_move_dir(Base s){
    switch(s){
        case Base::S1D: case Base::S1D_PR: case Base::S3D: case Base::S3D_PR: return -1; // D
        default: return +1; // G
    }
}

struct Rule { char w; Base qprev; };
static Rule T[8][2];

struct Tape{
    vector<char> L,R; long min1=numeric_limits<long>::max(), max1=numeric_limits<long>::min();
    char& cell(long p){
        if(p>=0){ size_t i=(size_t)p; if(i>=R.size()) R.resize(i+1,'0'); return R[i]; }
        size_t j=(size_t)(-p-1); if(j>=L.size()) L.resize(j+1,'0'); return L[j];
    }
    char read(long p) const{
        if(p>=0){ size_t i=(size_t)p; return (i<R.size()? R[i]:'0'); }
        size_t j=(size_t)(-p-1); return (j<L.size()? L[j]:'0');
    }
    void set_and_update(long p, char v){
        char& ref=cell(p); if(ref==v) return;
        if(v=='1'){ if(p<min1) min1=p; if(p>max1) max1=p; }
        else if(ref=='1'&&(p==min1||p==max1)){
            long Lb=-(long)L.size(), Rb=(long)R.size()-1; bool f=false;
            if(p==min1){
                for(long t=min1+1;t<=Rb;++t) if(read(t)=='1'){ min1=t; f=true; break; }
                if(!f){ for(long t=min1-1;t>=Lb;--t) if(read(t)=='1'){ min1=t; f=true; break; } }
                if(!f){ min1=numeric_limits<long>::max(); max1=numeric_limits<long>::min(); }
            }else{
                for(long t=max1-1;t>=Lb;--t) if(read(t)=='1'){ max1=t; f=true; break; }
                if(!f){ for(long t=max1+1;t<=Rb;++t) if(read(t)=='1'){ max1=t; f=true; break; } }
                if(!f){ min1=numeric_limits<long>::max(); max1=numeric_limits<long>::min(); }
            }
        }
        ref=v;
    }
    pair<string,string> view(long h){
        (void)cell(h);
        long Lb=h,Rb=h; if(min1<=max1){ if(min1<Lb) Lb=min1; if(max1>Rb) Rb=max1; }
        size_t len=(size_t)(Rb-Lb+1); string line(len,'0');
        for(long p=Lb;p<=Rb;++p) line[(size_t)(p-Lb)]=read(p);
        string under; under.assign((size_t)(h-Lb),' '); under.push_back('^');
        return {line,under};
    }
};

struct TM{
    Tape tape; long h; Base q;
    TM(const string& word,long head,Base q0):h(head),q(q0){
        tape.R.assign(word.begin(),word.end());
        for(size_t i=0;i<word.size();++i) if(word[i]=='1'){ long ii=(long)i; if(ii<tape.min1)tape.min1=ii; if(ii>tape.max1)tape.max1=ii; }
        if(tape.R.empty()) tape.R.push_back('0');
    }
    void step(){
        h += inverse_move_dir(q);
        (void)tape.cell(h);

        char r = tape.read(h);

        const Rule& R = T[(int)q][ (r=='0')?0:1 ];
        tape.set_and_update(h, R.w);
        q = R.qprev;
    }
    pair<string,string> view(){ return tape.view(h); }
};

static void build_table(){
    auto add=[&](Base q, char in, char w, Base qprev){
        T[(int)q][ (in=='0')?0:1 ] = Rule{ w, qprev };
    };

    // (3G', 0, 1, 3G,  R)
    // (3G', 1, 1, 1D,  L)
    add(Base::S3G_PR,'0','1', Base::S3G);
    add(Base::S3G_PR,'1','1', Base::S1D);

    // (3D,  0, 0, 3G', R)
    // (3D,  1, 1, 1G', R)
    add(Base::S3D,'0','0', Base::S3G_PR);
    add(Base::S3D,'1','1', Base::S1G_PR);

    // (1G', 0, 1, 3G', R)
    // (1G', 1, 0, 1G,  R)
    add(Base::S1G_PR,'0','1', Base::S3G_PR);
    add(Base::S1G_PR,'1','0', Base::S1G);

    // (1D,  0, 0, 3D, L)
    // (1D,  1, 0, 1G', R)
    add(Base::S1D,'0','0', Base::S3D);
    add(Base::S1D,'1','0', Base::S1G_PR);

    // (3G,  0, 0, 3D', L)
    // (3G,  1, 1, 1D', L)
    add(Base::S3G,'0','0', Base::S3D_PR);
    add(Base::S3G,'1','1', Base::S1D_PR);

    // (3D', 0, 1, 3D,  L)
    // (3D', 1, 1, 1G,  R)
    add(Base::S3D_PR,'0','1', Base::S3D);
    add(Base::S3D_PR,'1','1', Base::S1G);

    // (1G,  0, 0, 3G,  R)
    // (1G,  1, 0, 1D', L)
    add(Base::S1G,'0','0', Base::S3G);
    add(Base::S1G,'1','0', Base::S1D_PR);

    // (1D', 0, 1, 3D',  L)
    // (1D', 1, 0, 1D,  L)
    add(Base::S1D_PR,'0','1', Base::S3D_PR);
    add(Base::S1D_PR,'1','0', Base::S1D);
}

int main(int argc,char**argv){
    ios::sync_with_stdio(false); cin.tie(nullptr);
    // ./inversa <pasos> <palabra> <cabezal> <estado>
    if(argc!=5){ cout<<"error\n"; return 1; }
    long pasos=strtoll(argv[1],nullptr,10);
    string palabra=argv[2];
    long pos=strtoll(argv[3],nullptr,10);
    string sst=argv[4];
    if(pasos<=0||palabra.empty()||!all_of(palabra.begin(),palabra.end(),[](char c){return c=='0'||c=='1';})||pos<0||pos>=(long)palabra.size()){ cout<<"error\n"; return 1; }
    Base q0; if(!parse_state(sst,q0)){ cout<<"error\n"; return 1; }

    build_table();
    TM m(palabra,pos,q0);

    for(long step=0; step<pasos; ++step){
        auto [l1,u1]=m.view();
        cout<<l1<<"\n"<<u1<<"\n";
        cout<<"Paso "<<step<<" (antes) | Estado="<<to_string_base(m.q)<<"\n";
        m.step();
        auto [l2,u2]=m.view();
        cout<<l2<<"\n"<<u2<<"\n";
        cout<<"Paso "<<step<<" (despues) | Estado="<<to_string_base(m.q)<<"\n";
        cout<<"----\n";
    }
    auto [lf,uf]=m.view();
    cout<<lf<<"\n"<<uf<<"\n";
    cout<<"Estado="<<to_string_base(m.q)<<"\n";
    return 0;
}
