
#include <string.h>
#include <stdlib.h>
#include <time.h>

#include <iostream>

#include <boost/program_options.hpp>
using namespace boost::program_options;

#include "satbasic.hpp"

void default_settings()
{
    ave_weight = 1;
    delta_total_weight = 0;
}

bool parse_arguments(int argc, char **argv)
{
    default_settings();

    try
    {
        options_description desc{"options"};
        desc.add_options()
            ("help,h", "Help")
            ("inst", value<std::string>()->required(), "SAT instance file name")
            ("seed", value<int>()->default_value((int)time(NULL)), "Random seed")
            ("max_tries", value<int>()->default_value(1000000000))
            ("max_flips", value<int>()->default_value(2000000000))
            ("aspiration", value<int>()->default_value(0))
            ("swt_threshold", value<int>()->default_value(50))
            ("swt_p", value<float>()->default_value(0.3))
            ("swt_q", value<float>()->default_value(0.7))
            ("ls_no_improv_steps", value<int>()->default_value(2000000))
#ifdef USE_RESULT
            ("result_file", value<std::string>())
            ("samerate", value<float>(), "Same rate of result")
#endif
#ifdef USE_PREDICT
            ("gpu_list", value<std::string>()->default_value(""))
            ("load_model", value<std::string>()->required())
            ("predict_file", value<std::string>()->default_value(""))
#endif
            ;

        variables_map vm;
        store(parse_command_line(argc, argv, desc), vm);
        notify(vm);

        inst = vm["inst"].as<std::string>();
        seed = vm["seed"].as<int>();
        max_tries = vm["max_tries"].as<int>();
        max_flips = vm["max_flips"].as<int>();
        aspiration_active = (bool)(vm["aspiration"].as<int>());
        threshold = vm["swt_threshold"].as<int>();
        p_scale = vm["swt_p"].as<float>();
        q_scale = vm["swt_q"].as<float>();
        ls_no_improv_times = vm["ls_no_improv_steps"].as<int>();

#ifdef USE_RESULT
        result_samerate = (int)(vm["samerate"].as<float>() * RAND_MAX);
        result_file = vm["result_file"].as<std::string>();
#endif
#ifdef USE_PREDICT
        gpu_list = vm["gpu_list"].as<std::string>();
        load_model = vm["load_model"].as<std::string>();
        predictfile = vm["predict_file"].as<std::string>();
#endif
    }
    catch (const error &ex)
    {
        std::cerr << ex.what() << '\n';
        return false;
    }

    return true;
}
