#pragma once
#include <string>
#include <array>
#include <cstdint>

extern const std::array<std::string,8> STATE_LABELS;

int state_index_from_label(const std::string& s);

enum class Base : std::uint8_t {
    S1D,
    S1D_PR,
    S1G,
    S1G_PR,
    S3D,
    S3D_PR,
    S3G,
    S3G_PR
};

std::string to_string_base(Base s);
bool parse_state(std::string s, Base& out);

struct RunResult {
    bool ok;
    std::string word_out;
    long pos_out;
    std::string state_out;
};

RunResult run_original(int pasos, const std::string& palabra, long pos, const std::string& estado);
RunResult run_inversa(int pasos, const std::string& palabra, long pos, const std::string& estado);
