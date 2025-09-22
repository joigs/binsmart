#include <array>
#include <deque>
#include <iostream>
#include <string>
#include <algorithm>

using namespace std;


enum class State : uint8_t { S1D, S1D_PR, S1G, S1G_PR, S3D, S3D_PR, S3G, S3G_PR };

static inline bool isD(State s){
    return s==State::S1D || s==State::S1D_PR || s==State::S3D || s==State::S3D_PR;
}
static inline bool isG(State s){
    return s==State::S1G || s==State::S1G_PR || s==State::S3G || s==State::S3G_PR;
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

static constexpr array<array<Rule,2>,8> T = {
    {{{ {'1', State::S1D_PR}, {'1', State::S3G_PR} }},
        {{ {'1', State::S1G   }, {'1', State::S3G   } }},
        {{ {'1', State::S1G_PR}, {'1', State::S3D_PR} }},
        {{ {'1', State::S1D   }, {'1', State::S3D   } }},
        {{ {'0', State::S1D   }, {'0', State::S3D_PR} }},
        {{ {'0', State::S3G   }, {'0', State::S1D_PR} }},
        {{ {'0', State::S1G   }, {'0', State::S3G_PR} }},
        {{ {'0', State::S3D   }, {'0', State::S1G_PR} }},
}};


struct TMH {
    deque<char> tape;
    long h;
    State q;

    TMH(const string& word, long head_index, State q0)
        : tape(word.begin(), word.end()), h(head_index), q(q0)
    { if(tape.empty()) tape.push_back('0'); }

    inline void ensure_cell(long idx){
        if(idx < 0){
            while(idx < 0){ tape.push_front('0'); ++idx; ++h; }
        }
        while(idx >= (long)tape.size()) tape.push_back('0');
    }

    inline void step(){
        ensure_cell(h);
        char r = tape[(size_t)h];
        const Rule& rule = T[(int)q][ (r=='0')?0:1 ];
        tape[(size_t)h] = rule.write;
        q = rule.next;
        h += move_from(q);
        ensure_cell(h);
    }

    pair<string,string> view_with_head(){
        ensure_cell(h);

        size_t n = tape.size();
        size_t first1 = n, last1 = 0;
        for(size_t i=0;i<n;i++){ if(tape[i]=='1'){ first1=i; break; } }
        for(size_t i=n;i>0;i--){ if(tape[i-1]=='1'){ last1=i-1; break; } }

        size_t hh = (size_t)h;

        size_t L, R;
        if(first1==n){
            L = hh; R = hh + 1;
        }else{
            L = min(first1, hh);
            R = max(last1, hh) + 1;
        }

        string line; line.reserve(R-L);
        for(size_t i=L;i<R;i++) line.push_back(tape[i]);

        string under(hh - L, ' ');
        under.push_back('^');

        return {line, under};
    }
};

int main(int argc, char** argv){
    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    if(argc != 5){ cout << "Error\n"; return 1; }

    long pasos = strtoll(argv[1], nullptr, 10);
    string palabra = argv[2];
    long pos = strtoll(argv[3], nullptr, 10);
    string sstate = argv[4];

    if(pasos <= 0){ cout << "Error\n"; return 1; }
    if(palabra.empty() || !all_of(palabra.begin(), palabra.end(),
        [](char c){ return c=='0' || c=='1'; })){ cout << "Error\n"; return 1; }
    if(pos < 0 || pos >= (long)palabra.size()){ cout << "Error\n"; return 1; }

    State q0;
    if(!parse_state(sstate, q0)){ cout << "Error\n"; return 1; }

    TMH m(palabra, pos, q0);

    for(long step=0; step<pasos; ++step){
        auto vw = m.view_with_head();
        cout << vw.first << "\n" << vw.second << "\n";
        cout << "Paso " << step << " | Estado=" << to_string_state(m.q) << "\n";
        m.step();
    }

    auto vw = m.view_with_head();
    cout << vw.first << "\n" << vw.second << "\n";
    cout << "Estado=" << to_string_state(m.q) << "\n";
    return 0;
}
