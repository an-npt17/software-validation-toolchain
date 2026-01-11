import argparse
import json
import os
import re
import time

import google.generativeai as genai
from dotenv import load_dotenv
from google.api_core import exceptions as google_exceptions

load_dotenv()
# Set up Gemini API
api_key = os.environ.get("GOOGLE_API_KEY") or os.environ.get("GEMINI_API_KEY")
if not api_key:
    raise ValueError("GOOGLE_API_KEY environment variable is not set")
genai.configure(api_key=api_key)


def chat_completion(
    messages, model="gemini-2.5-flash-lite", temperature=0.7, max_retries=5
):
    # Convert OpenAI message format to Gemini format
    system_instruction = None
    chat_messages = []

    for msg in messages:
        if msg["role"] == "system":
            system_instruction = msg["content"]
        elif msg["role"] == "user":
            chat_messages.append({"role": "user", "parts": [msg["content"]]})
        elif msg["role"] == "assistant":
            chat_messages.append({"role": "model", "parts": [msg["content"]]})

    model_instance = genai.GenerativeModel(
        model_name=model, system_instruction=system_instruction
    )

    retry_count = 0
    base_wait_time = 1  # Start with 1 second

    while retry_count <= max_retries:
        try:
            # Start chat with history (exclude the last message as it will be sent separately)
            if len(chat_messages) > 1:
                chat = model_instance.start_chat(history=chat_messages[:-1])
                response = chat.send_message(
                    chat_messages[-1]["parts"][0],
                    generation_config=genai.types.GenerationConfig(
                        temperature=temperature
                    ),
                )
            else:
                # If only one message, send it directly
                chat = model_instance.start_chat(history=[])
                response = chat.send_message(
                    chat_messages[0]["parts"][0],
                    generation_config=genai.types.GenerationConfig(
                        temperature=temperature
                    ),
                )

            return response.text

        except google_exceptions.ResourceExhausted as e:
            # Handle 429 rate limit error
            error_msg = str(e)

            # Check if this is a daily quota limit (not just rate limit)
            is_daily_quota = 'PerDay' in error_msg or 'quota_value' in error_msg

            retry_count += 1
            if retry_count > max_retries:
                if is_daily_quota:
                    print(f"\n{'='*60}")
                    print("DAILY QUOTA EXCEEDED")
                    print(f"{'='*60}")
                    print("You've hit the daily quota limit for the Google API.")
                    print("Options:")
                    print("  1. Wait until your quota resets (usually 24 hours)")
                    print("  2. Upgrade your API plan at: https://ai.google.dev/pricing")
                    print("  3. Use a different model with higher quota")
                    print(f"{'='*60}\n")
                else:
                    print(f"Max retries ({max_retries}) reached. Giving up.")
                raise

            # Try to extract wait time from error message or metadata
            wait_time = base_wait_time * (2 ** (retry_count - 1))  # Exponential backoff

            # Try to extract retry_delay from exception metadata
            if hasattr(e, 'details') and e.details:
                try:
                    # Parse retry_delay from error details if available
                    details_str = str(e.details)
                    if 'retry_delay' in details_str or 'seconds' in details_str:
                        # Look for seconds field in the error
                        seconds_match = re.search(r'seconds[:\s]+(\d+)', details_str)
                        if seconds_match:
                            wait_time = int(seconds_match.group(1)) + 2  # Add buffer
                except Exception:
                    pass

            # Look for various retry patterns in error message
            retry_patterns = [
                r'retry in (\d+(?:\.\d+)?)\s*s',  # "retry in 31.954905609s"
                r'retry after (\d+)',              # "Retry after 30"
                r'retry in (\d+)',                 # "retry in 30"
            ]

            for pattern in retry_patterns:
                retry_match = re.search(pattern, error_msg, re.IGNORECASE)
                if retry_match:
                    # Round up and add small buffer
                    wait_time = int(float(retry_match.group(1))) + 2
                    break

            print(
                f"Rate limit hit (429). Waiting {wait_time} seconds before retry {retry_count}/{max_retries}..."
            )
            time.sleep(wait_time)

        except Exception as e:
            # Handle other exceptions
            print(f"Error during API call: {type(e).__name__}: {e}")
            raise

    return response.text


def extract_code(response):
    for tag in [
        "```code",
        "```dafny",
        "```c",
        "```whyml",
        "```java",
        "```cmbc",
        "```why3",
        "```rust",
        "```promela",
        "```spin",
        "```pml",
        "```",
    ]:
        start = response.find(tag)
        if start != -1:
            end = response.find("```", start + len(tag))
            if end != -1:
                return response[start + len(tag) : end].strip(), tag[3:]
    return None, None


def extract_coherence(response):
    start = response.find("/answer{")
    end = response.find("}", start)
    if start != -1 and end != -1:
        return response[start + len("/answer{") : end].strip()
    return None


def form_query_response(instruction, system_prompt, previous_context=None):
    messages = [{"role": "system", "content": system_prompt}]
    if previous_context:
        messages.extend(previous_context)
    messages.append({"role": "user", "content": instruction})
    return chat_completion(messages, model="gemini-2.5-flash-lite", temperature=0.3)


def read_tasks_in_order(folder_path):
    task_files = sorted(
        [
            f
            for f in os.listdir(folder_path)
            if f.startswith("task") and f.endswith(".txt")
        ],
        key=lambda x: int(x.split("task")[1].split(".txt")[0]),
    )
    return [
        {"file": f, "content": open(os.path.join(folder_path, f)).read()}
        for f in task_files
    ]


def save_to_file(path, *contents):
    with open(path, "w") as f:
        for content in contents:
            f.write(content)
            f.write("\n\n")


def eval_code(tool, code_string, tag, timeout=60):
    if tool == "verus":
        from verify import eval_verus as eval_verus

        return eval_verus(code_string, timeout)
    elif tool == "why3":
        from verify import eval_why3 as eval_why3

        return eval_why3(code_string, timeout)
    elif tool == "dafny":
        from verify import eval_dafny as eval_dafny

        return eval_dafny(code_string, timeout)
    elif tool == "framac":
        from verify import eval_framac as eval_framac

        return eval_framac(code_string, timeout)
    elif tool == "verifast":
        from verify import eval_verifast as eval_verifast

        return eval_verifast(code_string, timeout, tag)
    elif tool == "vercors":
        from verify import eval_vercors as eval_vercors

        return eval_vercors(code_string, timeout)
    elif tool == "cbmc":
        from verify import eval_cbmc as eval_cbmc

        return eval_cbmc(code_string, timeout)
    elif tool == "spin" or tool == "promela":
        from verify import eval_spin as eval_spin

        return eval_spin(code_string, timeout)
    else:
        return {"error": f"No eval implementation for tool: {tool}", "returncode": -1}


# === Main ===
def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--attempt", type=int, required=True, help="Attempt for each task"
    )
    parser.add_argument(
        "--timelimit", type=int, required=True, help="Time limit to run the tool"
    )

    args = parser.parse_args()
    attempt_limit = args.attempt
    time_limit = args.timelimit

    coherent_prompt_file = "../prompts/coherent_prompt.txt"
    with open(coherent_prompt_file, "r") as f:
        coherent_prompt = f.read()

    task_root = "../VerifyThisBenchXS"
    log_root = "../claude/results_relaxed_feedback"

    fill_todo_inst = "Complete the TODO fields in the solution template. Fix any potential syntax error as necessary. \n"
    error_feedback_inst = "Here is the error log. Fix the issues. \n"

    # ================ GENERATION ======================

    for year in sorted(os.listdir(task_root)):
        year_path = os.path.join(task_root, year)
        if not os.path.isdir(year_path):
            continue

        for taskname in sorted(os.listdir(year_path)):
            task_path = os.path.join(year_path, taskname)
            if not os.path.isdir(task_path):
                continue

            for tool in os.listdir(task_path):
                tool_path = os.path.join(task_path, tool)
                print(f"\nProcessing {year}/{taskname}/{tool}")
                log_dir = os.path.join(log_root, year, taskname, tool)
                os.makedirs(log_dir, exist_ok=True)

                # Read task description
                description_path = os.path.join(tool_path, "description.txt")
                if not os.path.exists(description_path):
                    print(f" Missing description.txt for {year}/{taskname}, skipping.")
                    continue

                description = open(description_path).read()

                system_prompt_file = f"../prompts/system_prompts/{tool}.txt"
                assert os.path.exists(system_prompt_file), (
                    f"Missing system prompt file: {system_prompt_file}"
                )
                system_prompt = open(system_prompt_file).read()

                for filename in sorted(os.listdir(tool_path)):
                    # Skip the two special cases:
                    if filename == "description.txt":
                        continue
                    name, _ext = os.path.splitext(filename)
                    if name == "solution":
                        continue

                    full_path = os.path.join(tool_path, filename)
                    if not os.path.isfile(full_path):
                        continue

                    template_solution = None
                    # Read the file
                    with open(full_path, "r", encoding="utf-8") as f:
                        template_solution = f.read()

                    task_context = [
                        {
                            "role": "user",
                            "content": f"Target this verification problem; plan out your steps and write your final answer:\n\n{description}. Your task is to complete a given template solution and fill in the TODO fields",
                        },
                        {"role": "assistant", "content": "OK, I'm ready to help."},
                    ]

                    print(f"Generating for {year}/{taskname}/{tool}/{filename}")

                    attempt = 1
                    error = None

                    starttime = time.time()

                    while attempt <= attempt_limit:
                        start = time.time()
                        refine_context = (
                            task_context.copy() if attempt == 1 else refine_context
                        )
                        query_inst = (
                            fill_todo_inst + f"{template_solution}"
                            if attempt == 1
                            else error_feedback_inst + f"{error}"
                        )

                        response = form_query_response(
                            query_inst, system_prompt, refine_context
                        )

                        code_response, tag = extract_code(response)
                        print(f"Generation takes {time.time() - start}s")
                        log_dir = os.path.join(
                            log_root, year, taskname, tool, str(attempt)
                        )
                        os.makedirs(log_dir, exist_ok=True)
                        # Save code
                        code_path = os.path.join(
                            log_dir, f"code_response_{filename}_{str(attempt)}"
                        )
                        save_to_file(code_path, code_response or "NO CODE FOUND")

                        # Save context
                        refine_context.extend(
                            [
                                {
                                    "role": "user",
                                    "content": query_inst + template_solution,
                                },
                                {"role": "assistant", "content": response},
                            ]
                        )
                        refine_context_path = os.path.join(
                            log_dir, f"refine_context_{filename}_{str(attempt)}.txt"
                        )
                        save_to_file(
                            refine_context_path, json.dumps(refine_context, indent=4)
                        )

                        # Save coherence
                        # Coherence context is the task description + template solution
                        start = time.time()
                        time.sleep(5)
                        coherence_check = form_query_response(
                            coherent_prompt,
                            system_prompt,
                            task_context
                            + [
                                {
                                    "role": "user",
                                    "content": fill_todo_inst + f"{template_solution}",
                                },
                                {"role": "assistant", "content": response},
                            ],
                        )
                        print(f"Coherence takes {time.time() - start}s")
                        coherence_response = extract_coherence(coherence_check)
                        correctness_path = os.path.join(
                            log_dir, f"coherence_check_{filename}_{str(attempt)}.txt"
                        )
                        save_to_file(
                            correctness_path,
                            coherence_check,
                            coherence_response or "NO COHERENCE FOUND",
                        )

                        verification_path = os.path.join(
                            log_dir, f"verification_{filename}_{str(attempt)}.txt"
                        )
                        if not code_response:
                            attempt += 1
                            error = "Your previous attemp did not contain any code."
                            save_to_file(verification_path, json.dumps("NO CODE FOUND"))
                            continue

                        print(
                            f"\nVerifying {year}/{taskname}/{filename}/{str(attempt)}"
                        )

                        start = time.time()
                        result = eval_code(tool, code_response, tag, time_limit)
                        print(f"Evaluation takes {time.time() - start}s")
                        save_to_file(verification_path, json.dumps(result, indent=2))
                        error = (
                            result["out"] + result["err"]
                            if not result["timed_out"]
                            else "Execution timed out."
                        )
                        # early stop is succeed and all goals verified.
                        # need partial as some tool return 0 when goals partially verified.
                        if result["succeed"] and not result["partial"]:
                            break
                        attempt += 1
                        time.sleep(5)
                    print(f"Task completed in {time.time() - starttime}s")


if __name__ == "__main__":
    main()
