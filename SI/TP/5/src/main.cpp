#include <iostream>
#include <vector>
#include <string>
#include <shader.h> // Help to load shaders from files
// Include GLEW : Always include it before glfw.h et gl.h :)
#include <GL/glew.h>    // OpenGL Extension Wrangler Library : http://glew.sourceforge.net/
#include <GL/glfw.h>    // Window, keyboard, mouse : http://www.glfw.org/
#include <glm/glm.hpp>  // OpenGL Mathematics : http://glm.g-truc.net/0.9.5/index.html
#include <glm/gtc/matrix_transform.hpp>
#include <glm/gtc/type_ptr.hpp>

#include <GLFW_define.h>
#include <Mesh.h>

// Dimensions de la fenêtre :
#define WIDTH 1000.0f
#define HEIGHT 800.0f

using namespace glm;
using namespace std;

int main() {

  cout << "Debut du programme..." << endl;

  //==================================================
  //============= Creation de la fenetre =============
  //==================================================


  // Initialisation de GLFW
  if(!glfwInit()) {
    cout << "Echec de l'initialisation de GLFW" << endl;
    exit(EXIT_FAILURE);
  }

  glfwOpenWindowHint(GLFW_FSAA_SAMPLES, 4); // Anti Aliasing
  glfwOpenWindowHint(GLFW_OPENGL_VERSION_MAJOR, 3); // OpenGL 3.3
  glfwOpenWindowHint(GLFW_OPENGL_VERSION_MINOR, 3);
  glfwOpenWindowHint(GLFW_OPENGL_FORWARD_COMPAT, GL_TRUE);
  glfwOpenWindowHint(GLFW_OPENGL_PROFILE, GLFW_OPENGL_CORE_PROFILE);

  // Ouverture d'une fenêtre en 1024x768
  // et creation d'un contexte OpenGL
  if(!glfwOpenWindow(WIDTH, HEIGHT, 0,0,0,0, 32,0, GLFW_WINDOW)) {
    cout << "Echec de l'ouverture de fenetre OpenGL" << endl;
    glfwTerminate();
    exit(EXIT_FAILURE);
  }

  // Definition du titre de la fenêtre
  glfwSetWindowTitle( "Polytech RICM 4 - TP5" );

  // Autorise GLFW a recevoir les appuis de touche
  glfwEnable( GLFW_STICKY_KEYS );

  // Initialisation de  GLEW
  glewExperimental = GL_TRUE;
  if(glewInit() != GLEW_OK) {
    cout << "Echec de l'initialisation de GLEW" << endl;
    exit(EXIT_FAILURE);
  }

  // Verification des donnees du contexte OpenGL
  const GLubyte* renderer = glGetString (GL_RENDERER);
  cout << "Carte Graphique : " << renderer << endl;

  const GLubyte* version = glGetString (GL_VERSION);
  cout << "Driver OpenGL : " << version << endl;


  //==================================================
  //================= Initialisation =================
  //==================================================

  cout << "Initialisations..." << endl;


  // Definition de la couleur du fond
  glClearColor(0.1, 0.1, 0.1, 0.0);

  //-------------------------------------------------
  // Initialisation du shader programm

  // Compilation du shader programm
  GLuint programID = LoadShaders( "../shader/vertex.glsl", "../shader/fragment.glsl" );
  cout << "programID = " << programID << endl;

  //-------------------------------------------------
  // Definition des sommets et indices du maillage (on recouvre l'ecran avec 4 sommets/2 triangles)
  vec3 vertices[] = {vec3(-1.0, -1.0, 0.0),
		     vec3(-1.0,  1.0, 0.0),
		     vec3( 1.0, -1.0, 0.0),
		     vec3( 1.0,  1.0, 0.0)};

  unsigned int indices[] = {0, 1, 3, 0, 3, 2};


  // Creation d'un VAO (c'est l'objet qui encapsule les VBOs et qu'on va manipuler)
  GLuint vaoID;
  glGenVertexArrays(1,&vaoID);
  glBindVertexArray(vaoID); // rendre ce VAO actif

  //==================================================
  // Done : Creation d'un buffer (VBO) pour les positions des sommets
  // avec vertexBufferID pour identifiant
  //==================================================

  GLuint vertexBufferID;
  glGenBuffers(1, &vertexBufferID);
  cout << "vertexBufferID = " << vertexBufferID << endl;

  // Definition de vertexBufferID comme le buffer courant
  glBindBuffer(GL_ARRAY_BUFFER, vertexBufferID);

  // Copie des donnees sur la carte graphique (dans vertexBufferID)
  glBufferData(GL_ARRAY_BUFFER, sizeof(vertices), vertices, GL_STATIC_DRAW);

  // Obtention de l'ID de l'attribut "in_position" dans programID
  GLuint vertexPositionID = glGetAttribLocation(programID, "in_position");

  // On autorise et indique a OpenGL comment lire les donnees
  glVertexAttribPointer(vertexPositionID,3,GL_FLOAT,GL_FALSE,0,(void*)0);
  glEnableVertexAttribArray(vertexPositionID);


  //==================================================
  // Creation d'un nouveau buffer pour les indices des triangles (topologie)
  //==================================================
  GLuint indiceBufferID;
  glGenBuffers(1, &indiceBufferID);

  // Definition de vertexBufferID comme le buffer courant
  glBindBuffer(GL_ELEMENT_ARRAY_BUFFER, indiceBufferID);

  // Copie des donnees sur la carte graphique (dans vertexBufferID)
  glBufferData(GL_ELEMENT_ARRAY_BUFFER, sizeof(indices),indices, GL_STATIC_DRAW);

  glBindVertexArray(0); // Désactiver le VAO


  //==================================================
  //=========== Debut des choses serieuses ===========
  //==================================================


  cout << "Debut de la boucle principale..." << endl;

  double init_time = glfwGetTime();
  double prec_time = init_time;
  double cur_time = init_time;

  char title[100];
  // Boucle de dessin
  do{
    // Nettoyage de la zone de dessin (couleurs+profondeurs)
    int w,h;
    glfwGetWindowSize(&w,&h);
    glClear(GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT);


    //==================================================
    //============= Calcul du Point de Vue =============
    //==================================================

    prec_time = cur_time;
    cur_time = glfwGetTime() - init_time;
    double delta_time = cur_time - prec_time;
    sprintf(title,"Polytech RICM 4 - TP5 - %2.0f FPS",1.0/ delta_time);
    glfwSetWindowTitle(title);

    // TODO: Interaction avec la camera


    //==================================================
    //===================== Dessin =====================
    //==================================================

    // Definition de programID comme le shader courant
    glUseProgram(programID);

    // TODO: Transmission des variables uniform aux shaders


    // set viewport, enable VAO and draw
    glViewport(0,0,w,h);
    glBindVertexArray(vaoID);
    glDrawElements(GL_TRIANGLES,6,GL_UNSIGNED_INT,0);
    glBindVertexArray(0);


    // Echange des zones de dessin buffers
    glfwSwapBuffers();

    cout << "Temps ecoule (s) : " << cur_time << "\r";
    cout.flush();


  } // Execution de la boucle...
  while( glfwGetKey( GLFW_KEY_ESC ) != GLFW_PRESS &&  // ... jusqu'a appui sur la touche ESC
	 glfwGetWindowParam( GLFW_OPENED )        );  // ... ou fermeture de la fenetre

  cout << endl;

  // Ferme GLFW et OpenGL
  glfwTerminate();



  //==================================================
  //============== Nettoyage la memoire ==============
  //==================================================

  // Liberation des buffers
  glDeleteBuffers(1, &vaoID);
  glDeleteBuffers(1, &vertexBufferID);
  glDeleteBuffers(1, &indiceBufferID);


  cout << "Fin du programme..." << endl;


  return EXIT_SUCCESS;
}
