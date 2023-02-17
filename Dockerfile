FROM bitnami/dotnet-sdk:6.0.403

RUN mkdir -p ./myApp/ptsv

COPY . ./myApp/ptsv

RUN touch ./RunAll.sh && \
    echo "cd examples && for file in *; do ../PTSV \"\$file\" -a -s -stack 104857600; done" >> ./RunAll.sh && \
    chmod +x ./RunAll.sh && \
    cd ./myApp/ptsv && \
    cp -R "./paper examples" ~/examples && \
    dotnet publish -r linux-x64 -p:PublishSingleFile=true --self-contained false && \
    cd PTSV/bin/Debug/net6.0/linux-x64/publish/ && \
    mv ./* ~
