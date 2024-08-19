class MemoryCell:
    def __init__(self):
        self.labeled = False
        self.son = None

def garbage_collection():
    root_cells = []  # List to store root cells
    all_cells = []   # List to store all cells
    free_cells = []  # List to store free cells

    # Mutator part
    while True:
        i = MemoryCell()
        k = MemoryCell()
        all_cells.extend([i, k])
        k.labeled = True
        i.son = k

        # Garbage collector part
        while True:
            # Label all root cells
            for cell in root_cells:
                cell.labeled = True
            
            M = len(root_cells)
            
            while True:
                M_old = M
                for i in all_cells:
                    if i.labeled and i.son and not i.son.labeled:
                        i.son.labeled = True
                        M += 1
                if M == M_old:
                    break
            
            for i in all_cells:
                if i.labeled:
                    i.labeled = False  # Delete label
                else:
                    free_cells.append(i)  # Collect cell i (it's garbage)
                    all_cells.remove(i)
            
            # Add the collected cells to the list of free cells
            # (This step is implicit as we're already adding to free_cells)

        # For demonstration purposes, let's break the infinite loop
        # In practice, this would run continuously
        break

    return free_cells

# Run the garbage collection
collected_cells = garbage_collection()
print(f"Number of cells collected as garbage: {len(collected_cells)}")