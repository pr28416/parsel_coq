import tempfile
import subprocess
import os
import requests

def coq_exec(code):
    print("Given code to verify:", code)
    r = requests.post("https://coq.livecode.ch/check", data = {'v': code})
    r.raise_for_status()
    j = r.json()
    print(j, type(j))
    if j['out']:
        print("Code outputted:", j['out'])
    if j['status']:
        print("Error executing code:", j['log'])
        raise Exception(j['log'])
    print("No issues")

    # Create a temporary file to store the code
    # assert "begin" in code
    # assert "sorry" not in code
    # with tempfile.NamedTemporaryFile(mode='w', suffix='.v', delete=False) as f:
    #     f.write(code)
    #     f.flush()
    #     # Execute the code
    #     try:
    #         subprocess.run(['coq', f.name], check=True)
    #     except subprocess.CalledProcessError:
    #         print("Error executing code: ", code)
    #         raise
    #     finally:
    #         os.remove(f.name)

CONSTS = {

    "num_completions": 64,
    "min_completions": 8,
    "num_completions_eval": 64,
    "eval_mode": False,
    
    "rate_limit_tokens_text": 16000,
    "exec_pre": "",
    "needs_indent": False,
    "fn_init": "Definition ",
    "exclude_init": ["from ", "import "],
    "fn_end": "return",
    "gen_stop": ["\nTheorem", "\nLemma"],
    "import": "import {name} helpers\n",
    "header_str": lambda name, arg_list: f"{name}{' '.join(f'({arg})' for arg in arg_list if arg.strip())}",
    "sig_helper": "(* Signature: {sig}\n *)",
    "desc_helper": "(* {name}. Description: {desc} *)\n",
    "ret_helper": "(* Returns: {ret} *)\n",
    "use_helper": "(* Applies: {uses} *)\n",
    "impl_helper": "{header}:\n{impls}\n{asserts}",
    "assert_helper": lambda assertion: "  {assertion} :=".format(
        assertion=assertion.replace('Example', '').strip()),
    "assert_check": lambda line: line.strip().startswith('Example'),
    "assert_break": lambda cur_assert: (cur_assert, None),
    "assert_format": "-- {assert_in}\n",
    "explain_helper":  "(* Reviewer: *)\n"
                        "(* Please explain the above function in one sentence with as much detail as possible. *)\n"
                        "(* In your one-sentence description, specify the range and domain of your function precisely. *)\n"
                        "(* Your description should be clear enough that someone could reimplement the function from it. *)\n"
                        "(* Author: *)\n"
                        "(* Sounds good, here's my one-sentence explanation of {name}: *)\n"
                        "(* {name} *)",
    "decompose_helper": "(* Let's decompose this lemma into two lemmas: *)\n"
                        "(* Lemma to decompose: *)\n"
                        "(* - {parsel_str} *)\n"
                        "(* Sublemmas in the same format of 'lamma_name(hypotheses): description': *)\n",
    "example_helper": "(* {example} *)\n",
    "missing_gen_helper": "(* Helper function for {parent_name} *)\n"
                    "(* Usage examples:\n"
                    "(* {examples_str}\n"
                    "(* Definition {missing_fn_name}( *)",
    "decompose_example_prefix": " - ",
    'extension': '.v',
    "output_fn": "(* ({output_str}) *)\n",
    "full_fn_str": "(* {desc} *)\n{fn_impl}\n",
    "get_assert_in": lambda assert_str: assert_str.split('==')[0].replace('assert', '').strip(),
    "exist_asserts": lambda _: True,
    "exec": coq_exec,
    "impl_filter": lambda _: True,
    # "impl_filter": lambda impl: "begin" in impl and "sorry" not in impl,
    "implicit_assert": True,
}