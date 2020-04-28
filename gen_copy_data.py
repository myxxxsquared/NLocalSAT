import argparse
import os
import shutil

def main(input_dir, train_dir, eval_dir, eval_num):
    files = sorted(os.listdir(input_dir))

    total_num = len(files)
    eval_num = int(total_num * eval_num)
    train_num = total_num - eval_num

    eval_files = files[:eval_num]
    train_files = files[eval_num:]

    os.makedirs(train_dir, exist_ok=True)
    os.makedirs(eval_dir, exist_ok=True)
    for f in eval_files:
        shutil.copy(os.path.join(input_dir, f), os.path.join(eval_dir, f))
    for f in train_files:
        shutil.copy(os.path.join(input_dir, f), os.path.join(train_dir, f))

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument('-i', '--input_dir', type=str, required=True)
    parser.add_argument('-t', '--train_dir', type=str, default=None)
    parser.add_argument('-e', '--eval_dir', type=str, default=None)
    parser.add_argument('-n', '--eval_num', type=float, default=0.2)
    args = parser.parse_args()
    input_dir = args.input_dir.rstrip('/')
    train_dir = args.train_dir or input_dir + '-train'
    eval_dir = args.eval_dir or input_dir + '-eval'
    eval_num = args.eval_num
    
    main(input_dir, train_dir, eval_dir, eval_num)
