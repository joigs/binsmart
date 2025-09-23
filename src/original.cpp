#include <vector>
#include <string>
#include <iostream>
#include <algorithm>
#include <limits>

using namespace std;

//./original <n_pasos> <palabra> <indice_cabezal> <estado>
enum class State : uint8_t { S1D, S1D_PR, S1G, S1G_PR, S3D, S3D_PR, S3G, S3G_PR };

static inline bool isD(State s){
    return s==State::S1D || s==State::S1D_PR || s==State::S3D || s==State::S3D_PR;
}
static inline int move_from(State next){ return isD(next)? +1 : -1; }

static string to_string_state(State s){
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
static bool parse_state(string s, State& out){
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


struct Rule { char write; State next; };
static constexpr Rule T[8][2] = {
    { {'1', State::S1D_PR}, {'1', State::S3G_PR} },
    { {'1', State::S1G   }, {'1', State::S3G   } },
    { {'1', State::S1G_PR}, {'1', State::S3D_PR} },
    { {'1', State::S1D   }, {'1', State::S3D   } },
    { {'0', State::S1D   }, {'0', State::S3D_PR} },
    { {'0', State::S3G   }, {'0', State::S1D_PR} },
    { {'0', State::S1G   }, {'0', State::S3G_PR} },
    { {'0', State::S3D   }, {'0', State::S1G_PR} },
};

struct TMH {
    vector<char> left, right;
    long h;
    State q;
    long min1, max1;

    TMH(const string& word, long head_index, State q0): h(head_index), q(q0) {
        right.reserve(max<size_t>(word.size(), 16));
        right.assign(word.begin(), word.end());
        min1 = numeric_limits<long>::max();
        max1 = numeric_limits<long>::min();
        for(size_t i=0;i<word.size();++i){
            if(word[i]=='1'){ if((long)i<min1) min1=(long)i; if((long)i>max1) max1=(long)i; }
        }
        if(right.empty()) right.push_back('0');
    }

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

    inline void widen1_on_write(long p, char after){
        if(after=='1'){
            if(p<min1) min1=p;
            if(p>max1) max1=p;
        }else{
            if(min1<=max1){
                if(p==min1){
                    long L = - (long)left.size();
                    long R = (long)right.size()-1;
                    bool found=false;
                    for(long t=min1+1; t<=R; ++t){ if(read(t)=='1'){ min1=t; found=true; break; } }
                    if(!found){
                        for(long t=min1-1; t>=L; --t){ if(read(t)=='1'){ min1=t; found=true; break; } }
                    }
                    if(!found){ min1=numeric_limits<long>::max(); max1=numeric_limits<long>::min(); }
                }else if(p==max1){
                    long L = - (long)left.size();
                    long R = (long)right.size()-1;
                    bool found=false;
                    for(long t=max1-1; t>=L; --t){ if(read(t)=='1'){ max1=t; found=true; break; } }
                    if(!found){
                        for(long t=max1+1; t<=R; ++t){ if(read(t)=='1'){ max1=t; found=true; break; } }
                    }
                    if(!found){ min1=numeric_limits<long>::max(); max1=numeric_limits<long>::min(); }
                }
            }
        }
    }

    inline void step(){
        char r = read(h);
        const Rule& rule = T[(int)q][ (r=='0')?0:1 ];
        char& ref = cell(h);
        if(ref!=rule.write){
            widen1_on_write(h, rule.write);
            if(ref=='1' && rule.write=='0') widen1_on_write(h, '0');
            ref = rule.write;
        }
        q = rule.next;
        h += move_from(q);
        (void)cell(h);
    }

    pair<string,string> view_with_head(){
        (void)cell(h);
        long L = h, R = h;
        if(min1<=max1){ if(min1<L) L=min1; if(max1>R) R=max1; }
        size_t len = (size_t)(R - L + 1);
        string line; line.resize(len);
        for(long p=L; p<=R; ++p) line[(size_t)(p-L)] = read(p);
        string under((size_t)(h - L), ' ');
        under.push_back('^');
        return {line, under};
    }
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

    TMH m(palabra, pos, q0);

    for(long step=0; step<pasos; ++step){
        auto [line, under] = m.view_with_head();
        cout << line << "\n" << under << "\n";
        cout << "Paso " << step + 1 << " | Estado=" << to_string_state(m.q) << "\n \n ------------- \n";
        m.step();
    }

    auto [line, under] = m.view_with_head();
    cout << line << "\n" << under << "\n";
    cout << "Estado=" << to_string_state(m.q) << "\n";
    return 0;
}
