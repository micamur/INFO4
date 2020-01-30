#include <iostream>
#include <shader.hpp> // Help to load shaders from files
// Include GLEW : Always include it before glfw.h et gl.h :)
#include <GL/glew.h>   // OpenGL Extension Wrangler Library : http://glew.sourceforge.net/
#include <GL/glfw.h>   // Window, keyboard, mouse : http://www.glfw.org/
#include <glm/glm.hpp> // OpenGL Mathematics : www.http://glm.g-truc.net/0.9.5/index.html

using namespace glm;
using namespace std;

int main()
{
  cout << "Debut du programme..." << endl;

  // Initialisation de GLFW
  if (!glfwInit())
  {
    cout << "Echec de l'initialisation de GLFW" << endl;
    exit(EXIT_FAILURE);
  }

  glfwOpenWindowHint(GLFW_FSAA_SAMPLES, 4);         // Anti Aliasing
  glfwOpenWindowHint(GLFW_OPENGL_VERSION_MAJOR, 2); // OpenGL 2.1
  glfwOpenWindowHint(GLFW_OPENGL_VERSION_MINOR, 1);

  // Ouverture d'une fenêtre en 1024x768
  // et creation d'un contexte OpenGL
  if (!glfwOpenWindow(1024, 768, 0, 0, 0, 0, 32, 0, GLFW_WINDOW))
  {
    cout << "Echec de l'ouverture de fenetre OpenGL" << endl;
    glfwTerminate();
    exit(EXIT_FAILURE);
  }

  // Définition du titre de la fenêtre
  glfwSetWindowTitle("Polytech RICM 4 - TP1");

  // Autorise GLFW a recevoir les appuis de touche
  glfwEnable(GLFW_STICKY_KEYS);

  // Initialisation de  GLEW
  if (glewInit() != GLEW_OK)
  {
    cout << "Echec de l'initialisation de GLEW" << endl;
    exit(EXIT_FAILURE);
  }

  // Vérification des données du contexte OpenGL
  const GLubyte *renderer = glGetString(GL_RENDERER);
  cout << "Carte Graphique : " << renderer << endl;

  const GLubyte *version = glGetString(GL_VERSION);
  cout << "Driver OpenGL : " << version << endl;

  cout << "Initialisation..." << endl;

  // Définition de la couleur du fond
  glClearColor(0.0f, 0.0f, 0.3f, 0.0f);

  // Compilation du shader program et generation de l'ID du Shader
  GLuint programID = LoadShaders("../shader/vertex2.glsl", "../shader/fragment.glsl");

  // On dit a OpenGL d'utiliser programID
  glUseProgram(programID);

  // Définition d'un vecteur
  // vec3 v0(-0.5f, -0.5f, +0.0f);
  // vec3 v1(+0.5f, -0.5f, +0.0f);
  // vec3 v2(+0.0f, +0.5f, +0.0f);

  // Définition d'un tableau de vecteurs

  /*
  // Triangle
  vec3 vertex[3];
  vertex[0] = vec3(-0.5f, -0.5f, +0.0f);
  vertex[1] = vec3(-0.5f, +0.5f, +0.0f);
  vertex[2] = vec3(+0.5f, -0.5f, +0.0f);
  */

   /*
  // Carré
  vec3 vertex[6];
  vertex[0] = vec3(-0.5f, -0.5f, +0.0f);
  vertex[1] = vec3(-0.5f, +0.5f, +0.0f);
  vertex[2] = vec3(+0.5f, -0.5f, +0.0f);
  vertex[3] = vec3(+0.5f, +0.5f, +0.0f);
  vertex[4] = vec3(+0.5f, -0.5f, +0.0f);
  vertex[5] = vec3(-0.5f, +0.5f, +0.0f);

  */

  /*
  // Maison
  vec3 vertex[9];
  vertex[0] = vec3(-0.5f, -0.5f, +0.0f);
  vertex[1] = vec3(-0.5f, +0.5f, +0.0f);
  vertex[2] = vec3(+0.5f, -0.5f, +0.0f);
  vertex[3] = vec3(+0.5f, +0.5f, +0.0f);
  vertex[4] = vec3(+0.5f, -0.5f, +0.0f);
  vertex[5] = vec3(-0.5f, +0.5f, +0.0f);
  vertex[6] = vec3(-0.5f, +0.5f, +0.0f);
  vertex[7] = vec3(+0.5f, +0.5f, +0.0f);
  vertex[8] = vec3(+0.0f, +0.75f, +0.0f);
  */

  /*
  // Points
  vec3 vertex[4];
  vertex[0] = vec3(-0.5f, -0.5f, +0.0f);
  vertex[1] = vec3(-0.5f, +0.5f, +0.0f);
  vertex[2] = vec3(+0.5f, -0.5f, +0.0f);
  vertex[3] = vec3(+0.5f, +0.5f, +0.0f);
  */

  /*
  // Noeud papillon
  vec3 vertex[8];
  vertex[0] = vec3(-0.5f, -0.5f, +0.0f);
  vertex[1] = vec3(-0.5f, +0.5f, +0.0f);
  vertex[2] = vec3(+0.5f, -0.5f, +0.0f);
  vertex[3] = vec3(+0.5f, +0.5f, +0.0f);
  vertex[4] = vec3(+0.5f, -0.5f, +0.0f);
  vertex[5] = vec3(-0.5f, +0.5f, +0.0f);
  vertex[6] = vec3(-0.5f, -0.5f, +0.0f);
  vertex[7] = vec3(+0.5f, +0.5f, +0.0f);
  */


  // Etoile
  vec3 vertex[7];
  vertex[0] = vec3(-0.25f, -0.5f, +0.0f);
  vertex[1] = vec3(-0.5f, +0.25f, +0.0f);
  vertex[2] = vec3(+0.0f, +0.75f, +0.0f);
  vertex[3] = vec3(+0.5f, +0.25f, +0.0f);
  vertex[4] = vec3(+0.25f, -0.5f, +0.0f);
  vertex[5] = vec3(-0.25f, -0.5f, +0.0f);
  vertex[6] = vec3(-0.5f, +0.25f, +0.0f);
  

  /*
  // Eventail
  vec3 vertex[6];
  vertex[0] = vec3(+0.0f, +0.0f, +0.0f);
  vertex[1] = vec3(-0.75f, +0.0f, +0.0f);
  vertex[2] = vec3(-0.5f, +0.5f, +0.0f);
  vertex[3] = vec3(+0.0f, +0.75f, +0.0f);
  vertex[4] = vec3(+0.5f, +0.5f, +0.0f);
  vertex[5] = vec3(+0.75f, +0.0f, +0.0f);
  */

  // Obtention de l'ID de l'attribut "vertex_position" dans programID
  GLuint vertexPositionID = glGetAttribLocation(programID, "vertex_position");

  // Creation d'un VAO et recuperation de son ID
  GLuint vaoID;
  glGenVertexArrays(1, &vaoID);
  // Définition de notre VAO comme object courant
  glBindVertexArray(vaoID);

  // Creation d'un VBO et recuperation de son ID
  GLuint vboID;
  glGenBuffers(1, &vboID);
  // Définition de notre VBO comme le buffer courant
  // et lie automatiquement ce VBO au VAO actif (i.e. vaoID)
  glBindBuffer(GL_ARRAY_BUFFER, vboID);

  // Copie de données vers le VBO
  glBufferData(GL_ARRAY_BUFFER, sizeof(vertex), vertex, GL_STATIC_DRAW);
  
  // On indique a OpenGL comment lire les données
  glEnableVertexAttribArray(vertexPositionID);
  glVertexAttribPointer(
    vertexPositionID, // ID de l'attribut a configurer
    3,                // nombre de composante par position (x, y, z)
    GL_FLOAT,         // type des composantes
    GL_FALSE,         // normalisation des composantes
    0,                // decalage des composantes
    (void *)0         // offset des composantes
  );

  glBindVertexArray(0); // on desactive le VAO

  glEnable(GL_VERTEX_PROGRAM_POINT_SIZE);

  cout << "Debut de la boucle principale..." << endl;
  unsigned int i = 0;

  // Boucle de dessin
  do
  {
    // Nettoyage de la zone de dessin
    glClear(GL_COLOR_BUFFER_BIT);

    // Contour du triangle uniquement
    glPolygonMode(GL_FRONT_AND_BACK, GL_LINE);

    glBindVertexArray(vaoID); // On active le VAO

    // on dessine le contenu de tous les VBOs (buffers) associes a ce VAO
    // glDrawArrays(GL_TRIANGLES, 0, 3); // avec le triangle 
    // glDrawArrays(GL_TRIANGLES, 0, 6); // avec le carré 
    // glDrawArrays(GL_TRIANGLES, 0, 9); // avec la maison
    // glDrawArrays(GL_POINTS, 0, 4); // avec les points
    // glDrawArrays(GL_LINES, 0, 8); // avec le noeud papillon
    // glDrawArrays(GL_LINE_STRIP, 0, 4); // avec les points
    // glDrawArrays(GL_LINE_LOOP, 0, 4); // avec les points
    glDrawArrays(GL_TRIANGLE_STRIP, 0, 7); // avec l'étoile
    // glDrawArrays(GL_TRIANGLE_FAN, 0, 6); // avec l'éventail

    glBindVertexArray(0); // On desactive le VAO

    /*
    // Triangle en mode immédiat
    glBegin(GL_TRIANGLES);
    glColor3f(1, 0.5, 1);
    glVertex3f(-0.5f, -0.5f, 0.0f);
    glColor3f(1, 0.5, 1);
    glVertex3f(0.5f, -0.5f, 0.0f);
    glColor3f(0, 0.5, 1);
    glVertex3f(0.0f, 0.5f, 0.0f);
    glEnd();
    */

    // Echange des zones de dessin buffers
    glfwSwapBuffers();

    glClearColor(0.0f, 0.0f + i / 1000.0f, 0.3f, 0.0f);

    cout << "Compteur : " << i++ << "\r";
    cout.flush();
  }
  // Execution de la boucle...
  while (glfwGetKey(GLFW_KEY_ESC) != GLFW_PRESS && // ... jusqu'a appui sur la touche ESC
         glfwGetWindowParam(GLFW_OPENED));         // ... ou fermeture de la fenetre

  cout << endl;

  // Ferme GLFW et OpenGL
  glfwTerminate();

  glDeleteBuffers(1, &vboID);
  glDeleteBuffers(1, &vaoID);

  cout << "Fin du programme..." << endl;

  return EXIT_SUCCESS;
}
