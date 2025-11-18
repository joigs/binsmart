#include "tm.hpp"
#include <vector>
#include <limits>
#include <algorithm>
#include <cctype>

const std::array<std::string,8> STATE_LABELS = {
    "1D","1D'","1G","1G'","3D","3D'","3G","3G'"
};

int state_index_from_label(const std::string& s) {
    Base b;
    if (!parse_state(s, b)) return -1;
    return (int)b;
}

std::string to_string_base(Base s) {
    switch(s) {
        case Base::S1D:    return "1D";
        case Base::S1D_PR: return "1D'";
        case Base::S1G:    return "1G";
        case Base::S1G_PR: return "1G'";
        case Base::S3D:    return "3D";
        case Base::S3D_PR: return "3D'";
        case Base::S3G:    return "3G";
        case Base::S3G_PR: return "3G'";
    }
    return "?";
}

bool parse_state(std::string s, Base& out) {
    for (char& c : s) c = (char)std::toupper((unsigned char)c);
    if (s == "1D")  { out = Base::S1D;    return true; }
    if (s == "1D'") { out = Base::S1D_PR; return true; }
    if (s == "1G")  { out = Base::S1G;    return true; }
    if (s == "1G'") { out = Base::S1G_PR; return true; }
    if (s == "3D")  { out = Base::S3D;    return true; }
    if (s == "3D'") { out = Base::S3D_PR; return true; }
    if (s == "3G")  { out = Base::S3G;    return true; }
    if (s == "3G'") { out = Base::S3G_PR; return true; }
    return false;
}

static int mv_from(Base s) {
    switch(s) {
        case Base::S1D:
        case Base::S1D_PR:
        case Base::S3D:
        case Base::S3D_PR:
            return +1;
        default:
            return -1;
    }
}

static int inverse_move_dir(Base s) {
    switch(s) {
        case Base::S1D:
        case Base::S1D_PR:
        case Base::S3D:
        case Base::S3D_PR:
            return -1;
        default:
            return +1;
    }
}

struct Tape {
    std::vector<char> L;
    std::vector<char> R;
    long min1;
    long max1;
    Tape() : min1(std::numeric_limits<long>::max()),
             max1(std::numeric_limits<long>::min()) {}

    char& cell(long p) {
        if (p >= 0) {
            std::size_t i = (std::size_t)p;
            if (i >= R.size()) R.resize(i + 1, '0');
            return R[i];
        }
        std::size_t j = (std::size_t)(-p - 1);
        if (j >= L.size()) L.resize(j + 1, '0');
        return L[j];
    }

    char read(long p) const {
        if (p >= 0) {
            std::size_t i = (std::size_t)p;
            return i < R.size() ? R[i] : '0';
        }
        std::size_t j = (std::size_t)(-p - 1);
        return j < L.size() ? L[j] : '0';
    }

    void set_and_update(long p, char v) {
        char& ref = cell(p);
        if (ref == v) return;
        if (v == '1') {
            if (p < min1) min1 = p;
            if (p > max1) max1 = p;
        } else if (ref == '1' && (p == min1 || p == max1)) {
            long Lb = -(long)L.size();
            long Rb = (long)R.size() - 1;
            bool f = false;
            if (p == min1) {
                for (long t = min1 + 1; t <= Rb; ++t) {
                    if (read(t) == '1') {
                        min1 = t;
                        f = true;
                        break;
                    }
                }
                if (!f) {
                    for (long t = min1 - 1; t >= Lb; --t) {
                        if (read(t) == '1') {
                            min1 = t;
                            f = true;
                            break;
                        }
                    }
                }
                if (!f) {
                    min1 = std::numeric_limits<long>::max();
                    max1 = std::numeric_limits<long>::min();
                }
            } else {
                for (long t = max1 - 1; t >= Lb; --t) {
                    if (read(t) == '1') {
                        max1 = t;
                        f = true;
                        break;
                    }
                }
                if (!f) {
                    for (long t = max1 + 1; t <= Rb; ++t) {
                        if (read(t) == '1') {
                            max1 = t;
                            f = true;
                            break;
                        }
                    }
                }
                if (!f) {
                    min1 = std::numeric_limits<long>::max();
                    max1 = std::numeric_limits<long>::min();
                }
            }
        }
        ref = v;
    }
};

struct Quint {
    char w;
    Base next;
    int mv;
};

struct Rule {
    char w;
    Base qprev;
};

struct TMForward {
    Tape tape;
    long h;
    Base q;

    TMForward(const std::string& word, long head, Base q0)
        : h(head), q(q0) {
        tape.R.assign(word.begin(), word.end());
        for (std::size_t i = 0; i < word.size(); ++i) {
            if (word[i] == '1') {
                long ii = (long)i;
                if (ii < tape.min1) tape.min1 = ii;
                if (ii > tape.max1) tape.max1 = ii;
            }
        }
        if (tape.R.empty()) tape.R.push_back('0');
    }

    void step(const Quint T[8][2]) {
        char r = tape.read(h);
        const Quint& R = T[(int)q][ (r == '0') ? 0 : 1 ];
        tape.set_and_update(h, R.w);
        h += R.mv;
        tape.cell(h);
        q = R.next;
    }
};

struct TMInverse {
    Tape tape;
    long h;
    Base q;

    TMInverse(const std::string& word, long head, Base q0)
        : h(head), q(q0) {
        tape.R.assign(word.begin(), word.end());
        for (std::size_t i = 0; i < word.size(); ++i) {
            if (word[i] == '1') {
                long ii = (long)i;
                if (ii < tape.min1) tape.min1 = ii;
                if (ii > tape.max1) tape.max1 = ii;
            }
        }
        if (tape.R.empty()) tape.R.push_back('0');
    }

    void step(const Rule T[8][2]) {
        h += inverse_move_dir(q);
        tape.cell(h);
        char r = tape.read(h);
        const Rule& R = T[(int)q][ (r == '0') ? 0 : 1 ];
        tape.set_and_update(h, R.w);
        q = R.qprev;
    }
};

RunResult run_original(int pasos, const std::string& palabra, long pos, const std::string& estado) {
    RunResult res;
    res.ok = false;
    res.word_out.clear();
    res.pos_out = 0;
    res.state_out.clear();

    if (pasos <= 0) return res;
    if (palabra.empty()) return res;
    if (!std::all_of(palabra.begin(), palabra.end(), [](char c){ return c=='0' || c=='1'; })) return res;
    if (pos < 0 || pos >= (long)palabra.size()) return res;

    Base q0;
    if (!parse_state(estado, q0)) return res;

    Quint T[8][2];
    auto add = [&](Base s, char in, Base nxt, char w) {
        T[(int)s][ (in == '0') ? 0 : 1 ] = Quint{ w, nxt, mv_from(nxt) };
    };

    add(Base::S3G_PR,'0', Base::S3D,   '0');
    add(Base::S3G_PR,'1', Base::S1G_PR,'0');
    add(Base::S3D,   '0', Base::S1D,   '0');
    add(Base::S3D,   '1', Base::S3D_PR,'0');
    add(Base::S1G_PR,'0', Base::S1D,   '1');
    add(Base::S1G_PR,'1', Base::S3D,   '1');
    add(Base::S1D,   '0', Base::S1D_PR,'1');
    add(Base::S1D,   '1', Base::S3G_PR,'1');
    add(Base::S3D_PR,'0', Base::S3G,   '0');
    add(Base::S3D_PR,'1', Base::S1D_PR,'0');
    add(Base::S1G,   '0', Base::S1G_PR,'1');
    add(Base::S1G,   '1', Base::S3D_PR,'1');
    add(Base::S3G,   '0', Base::S1G,   '0');
    add(Base::S3G,   '1', Base::S3G_PR,'0');
    add(Base::S1D_PR,'0', Base::S1G,   '1');
    add(Base::S1D_PR,'1', Base::S3G,   '1');

    TMForward m(palabra, pos, q0);
    for (int step = 0; step < pasos; ++step) m.step(T);

    std::string wout;
    if (m.tape.R.empty()) wout = "0";
    else wout.assign(m.tape.R.begin(), m.tape.R.end());

    res.ok = true;
    res.word_out = wout;
    res.pos_out = m.h;
    res.state_out = to_string_base(m.q);
    return res;
}

RunResult run_inversa(int pasos, const std::string& palabra, long pos, const std::string& estado) {
    RunResult res;
    res.ok = false;
    res.word_out.clear();
    res.pos_out = 0;
    res.state_out.clear();

    if (pasos <= 0) return res;
    if (palabra.empty()) return res;
    if (!std::all_of(palabra.begin(), palabra.end(), [](char c){ return c=='0' || c=='1'; })) return res;
    if (pos < 0 || pos >= (long)palabra.size()) return res;

    Base q0;
    if (!parse_state(estado, q0)) return res;

    Rule T[8][2];
    auto add = [&](Base q, char in, char w, Base qprev) {
        T[(int)q][ (in == '0') ? 0 : 1 ] = Rule{ w, qprev };
    };

    add(Base::S3G_PR,'0','1', Base::S3G);
    add(Base::S3G_PR,'1','1', Base::S1D);
    add(Base::S3D,'0','0', Base::S3G_PR);
    add(Base::S3D,'1','1', Base::S1G_PR);
    add(Base::S1G_PR,'0','1', Base::S3G_PR);
    add(Base::S1G_PR,'1','0', Base::S1G);
    add(Base::S1D,'0','0', Base::S3D);
    add(Base::S1D,'1','0', Base::S1G_PR);
    add(Base::S3G,'0','0', Base::S3D_PR);
    add(Base::S3G,'1','1', Base::S1D_PR);
    add(Base::S3D_PR,'0','1', Base::S3D);
    add(Base::S3D_PR,'1','1', Base::S1G);
    add(Base::S1G,'0','0', Base::S3G);
    add(Base::S1G,'1','0', Base::S1D_PR);
    add(Base::S1D_PR,'0','1', Base::S3D_PR);
    add(Base::S1D_PR,'1','0', Base::S1D);

    TMInverse m(palabra, pos, q0);
    for (int step = 0; step < pasos; ++step) m.step(T);

    std::string wout;
    if (m.tape.R.empty()) wout = "0";
    else wout.assign(m.tape.R.begin(), m.tape.R.end());

    res.ok = true;
    res.word_out = wout;
    res.pos_out = m.h;
    res.state_out = to_string_base(m.q);
    return res;
}
