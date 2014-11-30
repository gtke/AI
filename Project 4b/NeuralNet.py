import copy
import sys
from datetime import datetime
from math import exp
from random import random, randint, choice

class Perceptron(object):
    """
    Class to represent a single Perceptron in the net.
    """
    def __init__(self, inSize=1, weights=None):
        self.inSize = inSize+1#number of perceptrons feeding into this one; add one for bias
        if weights is None:
            #weights of previous layers into this one, random if passed in as None
            self.weights = [1.0]*self.inSize
            self.setRandomWeights()
        else:
            self.weights = weights
    
    def getWeightedSum(self, inActs):
        """
        Returns the sum of the input weighted by the weights.
        
        Inputs:
            inActs (list<float/int>): input values, same as length as inSize
        Returns:
            float
            The weighted sum
        """
        return sum([inAct*inWt for inAct,inWt in zip(inActs,self.weights)])
    
    def sigmoid(self, value):
        """
        Return the value of a sigmoid function.
        
        Args:
            value (float): the value to get sigmoid for
        Returns:
            float
            The output of the sigmoid function parametrized by 
            the value.
        """
        """YOUR CODE"""
        return (1 / (1.0 + exp((-1.0)*value)))
      
    def sigmoidActivation(self, inActs):                                       
        """
        Returns the activation value of this Perceptron with the given input.
        Same as rounded g(z) in book.
        Remember to add 1 to the start of inActs for the bias input.
        
        Inputs:
            inActs (list<float/int>): input values, not including bias
        Returns:
            int
            The rounded value of the sigmoid of the weighted input
        """
        return round(self.sigmoid(self.getWeightedSum([1.0] + inActs)))

    def sigmoidDeriv(self, value):
        """
        Return the value of the derivative of a sigmoid function.
        
        Args:
            value (float): the value to get sigmoid for
        Returns:
            float
            The output of the derivative of a sigmoid function
            parametrized by the value.
        """
        return self.sigmoid(value) * (1.0 - self.sigmoid(value)) 
        
    def sigmoidActivationDeriv(self, inActs):
        """
        Returns the derivative of the activation of this Perceptron with the
        given input. Same as g'(z) in book (note that this is not rounded.
        Remember to add 1 to the start of inActs for the bias input.
        
        Inputs:
            inActs (list<float/int>): input values, not including bias
        Returns:
            int
            The derivative of the sigmoid of the weighted input
        """
        return self.sigmoidDeriv(self.getWeightedSum([1.0] + inActs))
    
    def updateWeights(self, inActs, alpha, delta):
        """
        Updates the weights for this Perceptron given the input delta.
        Remember to add 1 to the start of inActs for the bias input.
        
        Inputs:
            inActs (list<float/int>): input values, not including bias
            alpha (float): The learning rate
            delta (float): If this is an output, then g'(z)*error
                           If this is a hidden unit, then the as defined-
                           g'(z)*sum over weight*delta for the next layer
        Returns:
            float
            Return the total modification of all the weights (sum of each abs(modification))
        """
        totalModification = 0
        inActs = [1] + inActs
        new_weights = []
        for i in range(0, len(inActs) ):
            new_weight = self.weights[i] + (alpha*delta*inActs[i])
            new_weights.append(new_weight)
            totalModification += new_weights[i] - self.weights[i]
        self.weights = new_weights
        if totalModification < 0: totalModification *= (-1)
        return totalModification
            
    def setRandomWeights(self):
        """
        Generates random input weights that vary from -1.0 to 1.0
        """
        for i in range(self.inSize):
            self.weights[i] = (random() + .0001) * (choice([-1,1]))
        
    def __str__(self):
        """ toString """
        outStr = ''
        outStr += 'Perceptron with %d inputs\n'%self.inSize
        outStr += 'Node input weights %s\n'%str(self.weights)
        return outStr

class NeuralNet(object):                                    
    """
    Class to hold the net of perceptrons and implement functions for it.
    """          
    def __init__(self, layerSize):#default 3 layer, 1 percep per layer
        """
        Initiates the NN with the given sizes.
        
        Args:
            layerSize (list<int>): the number of perceptrons in each layer 
        """
        self.layerSize = layerSize #Holds number of inputs and percepetrons in each layer
        self.outputLayer = []
        self.numHiddenLayers = len(layerSize)-2
        self.hiddenLayers = [[] for x in range(self.numHiddenLayers)]
        self.numLayers =  self.numHiddenLayers+1
        
        #build hidden layer(s)        
        for h in range(self.numHiddenLayers):
            for p in range(layerSize[h+1]):
                percep = Perceptron(layerSize[h]) # num of perceps feeding into this one
                self.hiddenLayers[h].append(percep)
 
        #build output layer
        for i in range(layerSize[-1]):
            percep = Perceptron(layerSize[-2]) # num of perceps feeding into this one
            self.outputLayer.append(percep)
            
        #build layers list that holds all layers in order - use this structure
        # to implement back propagation
        self.layers = [self.hiddenLayers[h] for h in xrange(self.numHiddenLayers)] + [self.outputLayer]
  
    def __str__(self):
        """toString"""
        outStr = ''
        outStr +='\n'
        for hiddenIndex in range(self.numHiddenLayers):
            outStr += '\nHidden Layer #%d'%hiddenIndex
            for index in range(len(self.hiddenLayers[hiddenIndex])):
                outStr += 'Percep #%d: %s'%(index,str(self.hiddenLayers[hiddenIndex][index]))
            outStr +='\n'
        for i in range(len(self.outputLayer)):
            outStr += 'Output Percep #%d:%s'%(i,str(self.outputLayer[i]))
        return outStr
    
    def feedForward(self, inActs):
        """
        Propagate input vector forward to calculate outputs.
        
        Args:
            inActs (list<float>): the input to the NN (an example) 
        Returns:
            list<list<float/int>>
            A list of lists. The first list is the input list, and the others are
            lists of the output values of all perceptrons in each layer.
        """
        """YOUR CODE"""
        inputs = list(inActs)
        result = []
        outputs = []
        for layer in self.layers:
            result.append(inputs)
            inputs = [perception.sigmoidActivation(inputs) for perception in layer]
        result.append(inputs)
        return result
    

    
    def backPropLearning(self, examples, alpha):
        """
        Run a single iteration of backward propagation learning algorithm.
        See the text and slides for pseudo code.
        
        Args: 
            examples (list<tuple<list<float>,list<float>>>):
              for each tuple first element is input(feature)"vector" (list)
              second element is output "vector" (list)
            alpha (float): the alpha to training with
        Returns
           tuple<float,float>
           
           A tuple of averageError and averageWeightChange, to be used as stopping conditions. 
           averageError is the summed error^2/2 of all examples, divided by numExamples*numOutputs.
           averageWeightChange is the summed absolute weight change of all perceptrons, 
           divided by the sum of their input sizes (the average weight change for a single perceptron).
        """
        #keep track of output
        averageError = 0
        averageWeightChange = 0
        numWeights = 0
        
        for example in examples:#for each example
            deltas = []#keep track of deltas to use in weight change
            
            """YOUR CODE"""
            """Get output of all layers"""
            output = self.feedForward(example[0])
            
            """
            Calculate output errors for each output perceptron and keep track 
            of error sum. Add error delta values to list.
            """
            errors = [y - x for x,y in zip(output[-1], example[1])]
            averageError += sum([(error**2)/2.0 for error in errors])
            deltas.append([error * percep.sigmoidActivationDeriv(output[-2])
                for error, percep in zip(errors, self.outputLayer)])

            
            """
            Backpropagate through all hidden layers, calculating and storing
            the deltas for each perceptron layer.
            Be careful to account for bias inputs! 
            """
            for h in range(self.numHiddenLayers): 
                delta = []
                # print self.layers[0][0]
                for i in range(self.layerSize[-2-h]): 
                    weights = [percep.weights[i+1] for percep in self.layers[-1-h]]
                    deriv = self.hiddenLayers[-1-h][i].sigmoidActivationDeriv(output[-3-h])
                    delta.append(deriv * sum([weight * d for weight, d in zip(weights, deltas[0])]))
                deltas = [delta] + deltas

            """
            Having aggregated all deltas, update the weights of the 
            hidden and output layers accordingly.
            """      
            for h in range(self.numLayers): 
                for i in range(self.layerSize[h+1]): 
                    # print self.layers[h][i]
                    averageWeightChange += self.layers[h][i].updateWeights(output[h], alpha, deltas[h][i])
                    numWeights += self.layers[h][i].inSize
        #end for each example
        
        """Calculate final output"""
        averageError /= (len(examples) * len(output[-1]))
        averageWeightChange /= numWeights
        return averageError, averageWeightChange
    
def buildNeuralNet(examples, alpha=0.1, weightChangeThreshold = 0.00008,hiddenLayerList = [1], maxItr = sys.maxint, startNNet = None):
    """
    Train a neural net for the given input.
    
    Args: 
        examples (tuple<list<tuple<list,list>>,
                        list<tuple<list,list>>>): A tuple of training and test examples
        alpha (float): the alpha to train with
        weightChangeThreshold (float):           The threshold to stop training at
        maxItr (int):                            Maximum number of iterations to run
        hiddenLayerList (list<int>):             The list of numbers of Perceptrons 
                                                 for the hidden layer(s). 
        startNNet (NeuralNet):                   A NeuralNet to train, or none if a new NeuralNet
                                                 can be trained from random weights.
    Returns
       tuple<NeuralNet,float>
       
       A tuple of the trained Neural Network and the accuracy that it achieved 
       once the weight modification reached the threshold, or the iteration 
       exceeds the maximum iteration.
    """
    examplesTrain,examplesTest = examples       
    numIn = len(examplesTrain[0][0])
    numOut = len(examplesTest[0][1])     
    time = datetime.now().time()
    if startNNet is not None:
        hiddenLayerList = [len(layer) for layer in startNNet.hiddenLayers]
    print "Starting training at time %s with %d inputs, %d outputs, %s hidden layers, size of training set %d, and size of test set %d"\
                                                    %(str(time),numIn,numOut,str(hiddenLayerList),len(examplesTrain),len(examplesTest))
    layerList = [numIn]+hiddenLayerList+[numOut]
    nnet = NeuralNet(layerList)                                                    
    if startNNet is not None:
        nnet =startNNet
    """
    YOUR CODE
    """
    iteration=0
    trainError=0
    weightMod=0
    
    """
    Iterate for as long as it takes to reach weight modification threshold
    """
    weightMod = float(sum(layerList))
    while weightMod > weightChangeThreshold and iteration <= maxItr: 
        trainError, weightMod = nnet.backPropLearning(examplesTrain, alpha)
        iteration += 1
        # print 'After %d iterations with training error %f and weight change %f'%(iteration,trainError,weightMod)
        # if iteration%10==0:
        #    print '! on iteration %d; training error %f and weight change %f'%(iteration,trainError,weightMod)
        # else :
        #    print '.',
          
    time = datetime.now().time()
    print 'Finished after %d iterations at time %s with training error %f and weight change %f'%(iteration,str(time),trainError,weightMod)
                
    """
    Get the accuracy of your Neural Network on the test examples.
    """ 
    
    testError = 0
    testGood = 0     
    
    testAccuracy=0#num correct/num total
    for example in examplesTest: 
        output = nnet.feedForward(example[0])
        if sum([abs(y - x) for x,y in zip(output[-1], example[1])]) == 0: 
            testGood += 1
        else: 
            testError += 1
    testAccuracy = float(testGood) / (testGood + testError)
    
    print 'Feed Forward Test correctly classified %d, incorrectly classified %d, test percent error  %f\n'%(testGood,testError,testAccuracy)
    
    """return something"""
    return (nnet, testAccuracy)



