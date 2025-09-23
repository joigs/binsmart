#include <vector>
#include <string>
#include <iostream>
#include <algorithm>
#include <limits>
#include <cstdint>
using namespace std;

enum class State : uint8_t { S1D, S1D_PR, S1G, S1G_PR, S3D, S3D_PR, S3G, S3G_PR };

static inline string to_string_state(State s){
    switch(s){
        case State::S1D:    return "1D";
        case State::S1D_PR: return "1D'";
        case State::S1G:    return "1G";
        case State::S1G_PR: return "1G'";
        case State::S3D:    return "3D";
        case State::S3D_PR: return "3D'";
        case State::S3G:    return "3G";
        case State::S3G_PR: return "3G'";
    }
    return "?";
}
static inline bool parse_state(string s, State& out){
    for(char& c: s) c = (char)toupper((unsigned char)c);
    if(s=="1D")  { out=State::S1D; return true; }
    if(s=="1D'") { out=State::S1D_PR; return true; }
    if(s=="1G")  { out=State::S1G; return true; }
    if(s=="1G'") { out=State::S1G_PR; return true; }
    if(s=="3D")  { out=State::S3D; return true; }
    if(s=="3D'") { out=State::S3D_PR; return true; }
    if(s=="3G")  { out=State::S3G; return true; }
    if(s=="3G'") { out=State::S3G_PR; return true; }
    return false;
}


struct Rule { char write; State next; int mv; };
static constexpr Rule T[8][2] = {
    { {'0', State::S3D,   -1},  {'0', State::S1G_PR, +1} },
    { {'1', State::S3D_PR,-1}, {'0', State::S1D,   -1} },
    { {'0', State::S3G,   +1}, {'0', State::S1D_PR,-1} },
    { {'1', State::S3G_PR,+1}, {'0', State::S1G,   +1} },
    {  {'0', State::S3G_PR,+1},  {'1', State::S1G_PR,+1} },
    { {'1', State::S3D,   -1}, {'1', State::S1G,   +1} },
    { {'0', State::S3D_PR,-1}, {'1', State::S1D_PR,-1} },
    {{'1', State::S3G,   +1},  {'1', State::S1D,   -1} },
};

struct Tape {
    vector<char> left, right;
    long min1, max1;

    Tape()
      : min1(numeric_limits<long>::max()),
        max1(numeric_limits<long>::min()) {}

    inline char& cell(long p){
        if(p>=0){
            size_t i=(size_t)p;
            if(i>=right.size()) right.resize(i+1,'0');
            return right[i];
        }else{
            size_t j=(size_t)(-p-1);
            if(j>=left.size()) left.resize(j+1,'0');
            return left[j];
        }
    }
    inline char read(long p) const {
        if(p>=0){
            size_t i=(size_t)p;
            return (i<right.size()? right[i]:'0');
        }else{
            size_t j=(size_t)(-p-1);
            return (j<left.size()? left[j]:'0');
        }
    }
    inline void set_and_update(long p, char v){
        char& ref = cell(p);
        if(ref==v) return;

        if(v=='1'){
            if(p<min1) min1=p;
            if(p>max1) max1=p;
        }else{
            if(ref=='1'){
                if(p==min1 || p==max1){
                    long L = - (long)left.size();
                    long R =   (long)right.size()-1;
                    if(p==min1){
                        bool found=false;
                        for(long t=min1+1; t<=R; ++t) if(read(t)=='1'){ min1=t; found=true; break; }
                        if(!found){
                            for(long t=min1-1; t>=L; --t) if(read(t)=='1'){ min1=t; found=true; break; }
                        }
                        if(!found){ min1=numeric_limits<long>::max(); max1=numeric_limits<long>::min(); }
                    }else{ // p==max1
                        bool found=false;
                        for(long t=max1-1; t>=L; --t) if(read(t)=='1'){ max1=t; found=true; break; }
                        if(!found){
                            for(long t=max1+1; t<=R; ++t) if(read(t)=='1'){ max1=t; found=true; break; }
                        }
                        if(!found){ min1=numeric_limits<long>::max(); max1=numeric_limits<long>::min(); }
                    }
                }
            }
        }
        ref = v;
    }

    inline pair<string,string> view(long head){
        (void)cell(head);
        long L=head, R=head;
        if(min1<=max1){ if(min1<L) L=min1; if(max1>R) R=max1; }

        size_t len=(size_t)(R-L+1);
        string line; line.resize(len);
        for(long p=L;p<=R;++p) line[(size_t)(p-L)] = read(p);

        string under;
        under.assign((size_t)(head - L), ' ');
        under.push_back('^');

        return {line, under};
    }
};

struct TM {
    Tape tape;
    long h;
    State q;

    TM(const string& word, long head_index, State q0) : h(head_index), q(q0) {
        tape.right.assign(word.begin(), word.end());
        for(size_t i=0;i<word.size();++i)
            if(word[i]=='1'){
                if((long)i<tape.min1) tape.min1=(long)i;
                if((long)i>tape.max1) tape.max1=(long)i;
            }
        if(tape.right.empty()) tape.right.push_back('0');
    }

    inline void step(){
        char r = tape.read(h);
        const Rule& rule = T[(int)q][ (r=='0')?0:1 ];
        tape.set_and_update(h, rule.write);
        q = rule.next;
        h += rule.mv;
        (void)tape.cell(h);
    }

    inline pair<string,string> view(){ return tape.view(h); }
};

int main(int argc, char** argv){
    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    if(argc != 5){ cout << "error\n"; return 1; }

    long pasos = strtoll(argv[1], nullptr, 10);
    string palabra = argv[2];
    long pos = strtoll(argv[3], nullptr, 10);
    string sstate = argv[4];

    if(pasos <= 0){ cout << "error\n"; return 1; }
    if(palabra.empty() || !all_of(palabra.begin(), palabra.end(),
        [](char c){ return c=='0' || c=='1'; })){ cout << "error\n"; return 1; }
    if(pos < 0 || pos >= (long)palabra.size()){ cout << "error\n"; return 1; }

    State q0;
    if(!parse_state(sstate, q0)){ cout << "error\n"; return 1; }

    TM m(palabra, pos, q0);

    for(long step=0; step<pasos; ++step){
        auto [line, under] = m.view();
        cout << line << "\n" << under << "\n";
        cout << "Paso " << step + 1 << " | Estado=" << to_string_state(m.q) << "\n \n ------------- \n";
        m.step();
    }

    auto [line, under] = m.view();
    cout << line << "\n" << under << "\n";
    cout << "Estado=" << to_string_state(m.q) << "\n";
    return 0;
}
