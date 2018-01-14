while true; 
do   
    echo; 
    echo '##################################'; 
    echo; 
    sleep 1;  
    pdflatex analysis.tex
    echo; 
    echo '##################################'; 
    echo; 
    sudo fbgs -xxl analysis.pdf > /dev/null;  
    echo ; 
done
