# NLocalSAT pretraining
# Press Ctrl+C when the network is trained to converge.
# Our original experiment takes about 168000 steps.

python sat.py \
    --logdir=train_origin \
    --gpu_list=3 \
    --load_model= \
    --train_steps=10000000 \
    --save_data_path= \
    --train_data=nlocal-pretraining/sattraindata \
    --eval_data=nlocal-pretraining/satevaldata \
    --eval_data_size=200 \
    --train_length=1000

# NLocalSAT fine-tuning
# modify train_length to the number of files under train-data and modify eval_data_size to the number of files under validation-data

python sat.py \
    --logdir=train_finalexp \
    --gpu_list=1 \
    --load_model=train/debug-168000 \
    --train_steps=10000000 \
    --save_data_path= \
    --train_data=${DATA_FOLDER}/train-data \
    --eval_data=${DATA_FOLDER}/vaildation-data \
    --eval_data_size=42 \
    --train_length=134

