import re
from collections import defaultdict

def analyze_log_file(file_path, error_pattern):
    error_buckets = defaultdict(list)
    
    # Compile the regex pattern
    error_regex = re.compile(error_pattern)
    
    with open(file_path, 'r') as file:
        for line_number, line in enumerate(file, 1):
            match = error_regex.search(line)
            if match:
                # Use the entire matched error as the key
                error_key = match.group(0)
                error_buckets[error_key].append(line_number)
    
    return error_buckets

def print_error_summary(error_buckets):
    for error, line_numbers in error_buckets.items():
        print(f"Error: {error}")
        print(f"Occurrences: {len(line_numbers)}")
        print(f"Line numbers: {', '.join(map(str, line_numbers))}")
        print()

# Example usage
log_file_path = 'path/to/your/logfile.log'
error_pattern = r'ERROR:.*'  # This pattern matches lines starting with "ERROR:"

error_buckets = analyze_log_file(log_file_path, error_pattern)
print_error_summary(error_buckets)
