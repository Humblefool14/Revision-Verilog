import pandas as pd
from collections import defaultdict

# Read the testcase_list.txt file
with open('testcase_list.txt', 'r') as file:
    lines = file.readlines()

# Parse the data
data = []
failures = defaultdict(list)

for line in lines:
    fields = line.strip().split(',')  # Assuming comma-separated values
    if len(fields) == 6:  # Ensure we have all expected fields
        timestamp, batch_number, random_seed, pass_fail, error_signature, testname = fields
        row_data = {
            'Timestamp': timestamp,
            'Batch Number': batch_number,
            'Random Seed': random_seed,
            'Pass/Fail': pass_fail,
            'Error Signature': error_signature,
            'Test Name': testname
        }
        data.append(row_data)
        
        # Check for failures and categorize them
        if pass_fail.lower() == 'fail':
            first_word = testname.split('_')[0]  # Assuming test names use underscores
            failures[first_word].append(row_data)

# Create a DataFrame for all data
df = pd.DataFrame(data)

# Save all data to Excel
df.to_excel('testcase_results.xlsx', index=False)

print("Excel file 'testcase_results.xlsx' has been created successfully.")

# Create separate sheets for failures
with pd.ExcelWriter('failure_analysis.xlsx') as writer:
    for category, failure_list in failures.items():
        failure_df = pd.DataFrame(failure_list)
        failure_df.to_excel(writer, sheet_name=category[:31], index=False)  # Excel sheet names are limited to 31 characters

print("Excel file 'failure_analysis.xlsx' with categorized failures has been created successfully.")

# Print summary of failures
print("\nFailure Summary:")
for category, failure_list in failures.items():
    print(f"{category}: {len(failure_list)} failures")